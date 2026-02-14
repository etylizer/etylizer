-module(ty_parser).

-compile([export_all, nowarn_export_all]).

-include("etylizer.hrl").

% TODO 
% the mixing of {local_ref, ...} and {node, ...} inside a BDD structure
% creates very ugly side effects and results in a complex implementation
% if we don't take care to ensure the correct ordering between all interactions of local_refs and nodes,
% one very easily generates invalid BDDs
% is there a more elegant solution providing the same guarantees with comparable efficiency?
% 
% TODO
% the local first unification might bring in more complexity than efficiency
% better to remove it, and only use global unification?

% a mapping from to-parse terms to a shorter form of local temporary references
-define(TERMREFS, ty_parser_term_references).

% a mapping from type references to type schemes (of the foreign interfaces)
-define(SYMTAB, ty_parser_symtab).

% a cache of already-parsed results
% determines which part of the type needs to be converted
% if something has been parsed before, replace it with a real reference
% if not, replace it with a local temporary reference and parse it, 
% replacing the temporary reference at the end by a real reference
-define(CACHE, ty_parser_cache).

% a mapping from temporary references to real references
% used for correct ordering inside a BDD 
% to be used by ty_node:compare/2 when comparing temporary references against real references
-define(LOCAL_TO_NODE_MAPPING, ty_parser_local_to_node_Mapping).

% a cache of discarded references which disappear after unification
% used to re-map local references to the unified reference, if possible
-define(UNIFY, ty_parser_unify).

% cache for unparsing nodes
-define(UNPARSE_CACHE, ty_parser_unparse_cache).

% mapping from node -> named used in unparsing
% this is a bit of a hack;
% during conversion, save all encountered {named, ...} types
% after conversion, convert them (which have not yet been converted yet) one by one again and save that reverse mapping
% TODO is there a more elegant solution for saving that information for unparsing?
-define(UNPARSE_NAMED_MAPPING, ty_parser_unparse_name_cache).
-define(UNPARSE_NAMED_QUEUE, ty_parser_unparse_queue).
-define(UNPARSE_NAMED_FINISHED, ty_parser_unparse_finish).

-define(ALL_ETS, [?CACHE, ?SYMTAB, ?TERMREFS, ?UNIFY, ?UNPARSE_CACHE, ?UNPARSE_NAMED_QUEUE, ?UNPARSE_NAMED_FINISHED, ?UNPARSE_NAMED_MAPPING, ?LOCAL_TO_NODE_MAPPING]).

-define(TY, dnf_ty_variable).
-define(NODE, ty_node).

-type temporary_ref() :: {local_ref, integer()}. % type references created for the queue
-type type() :: ?NODE:type().
-type type_descriptor() :: dnf_ty_variable:type().
-type ty_rec() :: ?TY:type().
-type ast_ty() :: ast:ty(). 
-type ety_ty_scheme() :: ast:ty_scheme().
-type ety_ref() :: ast:ty_ref() | mu_var. % also used as mu_var key in local_cache
-type ety_args() :: [ast:ty()].
-type database() :: {#{temporary_ref() => ty_rec()}, #{ty_rec() => [temporary_ref()]}}.
% the local cache should only consist of temporary references
% it is used both for recursive variable recursion
% and named type recursion at the same time
-type local_cache() :: #{ast:ty_mu_var() | {Ref :: ety_ref(), Args :: ety_args()} => temporary_ref()}.
-type queue() :: queue:queue({temporary_ref(), ast_ty()}).

% Subset types for split do_convert helpers.
% Each helper only receives the ast_ty() variants not matched by previous helpers.
-type ast_ty_predef() :: ast:ty_singleton() | ast:ty_bitstring() | ast:ty_some_list()
    | ast:ty_fun() | ast:ty_integer_range() | ast:ty_map_any() | ast:ty_map()
    | ast:ty_predef() | ast:ty_predef_alias()
    | ast:ty_tuple_any() | ast:ty_tuple() | ast:ty_var()
    | ast:ty_union() | ast:ty_intersection() | ast:ty_negation().
-type ast_ty_compound() :: ast:ty_cons() | ast:ty_list() | ast:ty_nonempty_list()
    | ast:ty_improper_list() | ast:ty_nonempty_improper_list()
    | ast:ty_full_fun() | ast:ty_map() | ast:ty_tuple()
    | ast:ty_var() | ast:ty_union() | ast:ty_intersection() | ast:ty_negation().
-type ast_ty_rewrite() :: ast:ty_cons() | ast:ty_list() | ast:ty_nonempty_list()
    | ast:ty_improper_list() | ast:ty_nonempty_improper_list()
    | ast:ty_full_fun() | ast:ty_map() | ast:ty_tuple()
    | ast:ty_var().
-type ast_ty_rewrite_list() :: ast:ty_cons() | ast:ty_list() | ast:ty_nonempty_list()
    | ast:ty_improper_list() | ast:ty_nonempty_improper_list()
    | ast:ty_full_fun() | ast:ty_map() | ast:ty_tuple().
-type ast_ty_rewrite_map() :: ast:ty_cons() | ast:ty_improper_list()
    | ast:ty_full_fun() | ast:ty_map() | ast:ty_tuple().
-type ast_ty_data() :: ast:ty_cons() | ast:ty_improper_list()
    | ast:ty_full_fun() | ast:ty_tuple().
-type ast_ty_non_named() :: ast:ty_mu() | ast:ty_mu_var() | ast_ty_predef().

% Subset types for debruijn helpers
% ast_ty() minus mu, mu_var
-type ast_ty_db1() :: ast:ty_singleton() | ast:ty_bitstring() | ast:ty_some_list()
    | ast:ty_fun() | ast:ty_integer_range() | ast:ty_map_any() | ast:ty_map()
    | ast:ty_predef() | ast:ty_predef_alias() | ast:ty_named()
    | ast:ty_tuple_any() | ast:ty_tuple() | ast:ty_var()
    | ast:ty_union() | ast:ty_intersection() | ast:ty_negation().
% ast_ty_db1() minus singleton, bitstring, empty_list, cons, list
-type ast_ty_db2() :: ast:ty_nonempty_list() | ast:ty_improper_list() | ast:ty_nonempty_improper_list()
    | ast:ty_fun() | ast:ty_integer_range() | ast:ty_map_any() | ast:ty_map()
    | ast:ty_predef() | ast:ty_predef_alias() | ast:ty_named()
    | ast:ty_tuple_any() | ast:ty_tuple() | ast:ty_var()
    | ast:ty_union() | ast:ty_intersection() | ast:ty_negation().
% ast_ty_db2() minus nonempty_list, improper_list, nonempty_improper_list, fun_simple, fun_any_arg, fun_full
-type ast_ty_db3() :: ast:ty_integer_range() | ast:ty_map_any() | ast:ty_map()
    | ast:ty_predef() | ast:ty_predef_alias() | ast:ty_named()
    | ast:ty_tuple_any() | ast:ty_tuple() | ast:ty_var()
    | ast:ty_union() | ast:ty_intersection() | ast:ty_negation().
% ast_ty_db3() minus range, map_any, map, predef, predef_alias, named
-type ast_ty_db4() :: ast:ty_tuple_any() | ast:ty_tuple() | ast:ty_var()
    | ast:ty_union() | ast:ty_intersection() | ast:ty_negation().
% Subset types for convert_back helpers
-type ast_ty_cb_other() :: ast:ty_singleton() | ast:ty_bitstring() | ast:ty_some_list()
    | ast:ty_fun() | ast:ty_integer_range() | ast:ty_map_any() | ast:ty_map()
    | ast:ty_predef() | ast:ty_predef_alias() | ast:ty_named()
    | ast:ty_tuple_any() | ast:ty_negation().
-type ast_ty_cb_rest() :: ast:ty_singleton() | ast:ty_bitstring() | ast:ty_empty_list()
    | ast:ty_fun() | ast:ty_integer_range() | ast:ty_map_any() | ast:ty_map()
    | ast:ty_predef() | ast:ty_predef_alias() | ast:ty_named()
    | ast:ty_tuple_any() | ast:ty_negation().


% global state
-spec init() -> _.
init() ->
  case ets:whereis(?SYMTAB) of
    undefined -> [ets:new(T, [public, set, named_table]) || T <- ?ALL_ETS];
    _ -> logger:info("~p state already initialized, skip init", [?MODULE])
  end,
  logger:debug("~p state initialized", [?MODULE]).

-spec clean() -> _.
clean() ->
  case ets:whereis(?SYMTAB) of
    undefined -> logger:info("~p state already deleted, skip clean", [?MODULE]);
    _ -> [ets:delete(T) || T <- ?ALL_ETS]
  end,
  logger:debug("~p state cleaned", [?MODULE]).

-spec set_symtab(symtab:t()) -> _.
set_symtab(SymTab) ->
  Types = symtab:get_types(SymTab),
  % elp:ignore W0034
  [ty_parser:extend_symtab(K, V) || {K, V} <- maps:to_list(Types)].

-spec lookup_ref(temporary_ref()) -> type(). 
lookup_ref(Ref) ->
  % we have already created the node beforehand, it needs to exist
  [{_, Node}] = ?assert_pattern([{Ref, _}], ets:lookup(?LOCAL_TO_NODE_MAPPING, Ref)),
  ?assert_type(Node, type()).

-spec create_ref(temporary_ref()) -> _.
create_ref(Ref) ->
  % we have already created the node beforehand, it needs to exist
  case ets:lookup(?LOCAL_TO_NODE_MAPPING, Ref) of
    [] -> ?assert_pattern(true, ets:insert_new(?LOCAL_TO_NODE_MAPPING, [{Ref, ty_node:new_ty_node()}]));
    _ -> ok
  end.

-spec parse(ast_ty()) -> type().
parse(RawTy) ->
  % io:format(user,"Parsing: ~w,~n", [RawTy]),
  % first: rename such that mu-binders have no collisions
  % use DeBruijn indexes and then convert back to fresh named variables
  % this has to be done anytime a {named, ...} reference is unfolded, too
  Ty = convert_back(debruijn(RawTy)),

  % create a reference, check if it is inside the cache
  LocalRef = new_local_ref(Ty),

  FinalResult = 
  case ets:lookup(?CACHE, LocalRef) of
    [{LocalRef, Node}] ->
      ?assert_type(Node, type());
    _ ->
      parse_convert(LocalRef, Ty)
  end,
  
  % generate the reverse named mapping at the end
  parse_named_mapping(),

  FinalResult.

-spec parse_named_mapping() -> ok.
parse_named_mapping() ->
  InQueue = ?assert_type(ets:tab2list(?UNPARSE_NAMED_QUEUE), [{ast_ty(), term()}]),
  lists:foreach(
    fun({N, _}) ->
      parse_named_mapping_entry(N)
    end, InQueue).

-spec parse_named_mapping_entry(ast_ty()) -> ok.
parse_named_mapping_entry(N) ->
  case ets:lookup(?UNPARSE_NAMED_FINISHED, N) of
    [] ->
      ets:insert(?UNPARSE_NAMED_FINISHED, {N, []}),
      ets:delete(?UNPARSE_NAMED_QUEUE, N),
      Mapping = parse(N),
      case ets:insert_new(?UNPARSE_NAMED_MAPPING, {Mapping, N}) of
        true ->
          ok;
        _ ->
          ok
      end;
    _ -> ok
  end.

-spec parse_convert(temporary_ref(), ast_ty()) -> type().
parse_convert(LocalRef, Ty) ->
  % 1. Convert to temporary local representation
  ({{NewR, NewTUnsorted}, _NewCache}) = convert(queue:from_list([{LocalRef, Ty}]), {_RefToTy = #{}, _TyToRef = #{}}, #{}),
  NewT = #{K => lists:usort(V) || K := V <- NewTUnsorted},

  % 2. (Locally) unify the results
  {UnifiedRef, UnifiedResult} = unify(LocalRef, {NewR, NewT}),

  % 3. create new type references and replace temporary ones
  ReplaceRefs = maps:from_list([{Ref, lookup_ref(Ref)} || Ref <- lists:sort(maps:keys(UnifiedResult))]),
  assert_replaced_refs_have_good_order(ReplaceRefs),
  {ReplacedRef, ReplacedResultsRaw} = utils:replace({UnifiedRef, UnifiedResult}, ReplaceRefs),
  ReplacedResults = maps:map(fun(_, V) -> dnf_ty_variable:reorder(V) end, ReplacedResultsRaw),

  % 4. define types
  % After replacement, temporary_ref()s are now type()s (i.e. {node, integer()})
  parse_define_types(?assert_type(ReplacedRef, type()), ReplaceRefs, ?assert_type(ReplacedResults, #{type() => type_descriptor()})).

-spec parse_define_types(type(), #{temporary_ref() => type()}, #{type() => type_descriptor()}) -> type().
parse_define_types(ReplacedRef, ReplaceRefs, ReplacedResults) ->
  Graph = #{K => lists:usort(V) || K := V <- #{Ref => collect_refs(Ref, ReplacedResults) || Ref := _ <- ReplacedResults}},
  RevGraph = tarjan:reverse_graph(Graph),

  {Scc, Condensed} = tarjan:condense(Graph),

  Components = lists:foldl(fun({Node, Root}, Acc) ->
    maps:update_with(Root, fun(Nodes) -> [Node | Nodes] end, [Node], Acc)
  end, #{}, lists:sort(maps:to_list(Scc))),

  Sort = tarjan:dfs(Condensed),
  Define = [maps:get(T, Components) || T <- Sort],

  parse_define_and_replace(ReplacedRef, ReplaceRefs, ReplacedResults, ?assert_type(RevGraph, #{type() => [type()]}), ?assert_type(Define, [[type()]])).

-spec parse_define_and_replace(type(), #{temporary_ref() => type()}, #{type() => type_descriptor()}, #{type() => [type()]}, [[type()]]) -> type().
parse_define_and_replace(ReplacedRef, ReplaceRefs, ReplacedResults, RevGraph, Define) ->
  {FinalReplacedRef, FinalReplaceRefs, FinalReplacedResults, _FinalLocalDefinitions} =
    define_and_replace_loop({ReplacedRef, ReplaceRefs, ReplacedResults, #{}}, Define, RevGraph),

  % define the final results globally
  parse_define_globals(FinalReplacedResults),

  % 5. update global cache
  parse_update_cache(FinalReplaceRefs),

  FinalReplacedRef.

-spec parse_define_globals(#{type() => type_descriptor()}) -> [type()].
parse_define_globals(Results) ->
  [?NODE:define(NodeRef, Record) || NodeRef := Record <- Results, is_not_defined(NodeRef, Record)].

-spec parse_update_cache(#{temporary_ref() => type()}) -> [ok].
parse_update_cache(ReplaceRefs) ->
  [case ets:insert_new(?CACHE, {LLocalRef, Node}) of
     true -> ok;
     false ->
       case ?assert_type(ets:lookup(?CACHE, LLocalRef), [{temporary_ref(), type()}]) of
         [{LLocalRef, Node}] -> ok;
         _ -> error(sanity)
       end
   end
   || LLocalRef := Node <- ReplaceRefs].

-type dar_acc() :: {type(), #{temporary_ref() => type()}, #{type() => type_descriptor()}, #{type_descriptor() => type()}}.

-spec define_and_replace_loop(dar_acc(), [[type()]], #{type() => [type()]}) -> dar_acc().
define_and_replace_loop(Acc, [], _RevGraph) -> Acc;
define_and_replace_loop(Acc, [Def | Rest], RevGraph) ->
  NewAcc = lists:foldl(fun(DefineOrReplace, AccInner) ->
    define_or_replace_step(DefineOrReplace, AccInner, RevGraph)
  end, Acc, Def),
  define_and_replace_loop(NewAcc, Rest, RevGraph).

-spec define_or_replace_step(type(), dar_acc(), #{type() => [type()]}) -> dar_acc().
define_or_replace_step(DefineOrReplace, Acc = {ReplacedRef0, Refmapping, ResultMapping0, LocalDefinitions0}, RevGraph) ->
  case ?NODE:is_defined(DefineOrReplace) of
    true -> % from previous parsing runs
      Acc;
    false ->
      ToDefineTy = maps:get(DefineOrReplace, ResultMapping0),
      case is_consed(ToDefineTy, LocalDefinitions0) of
        {true, N} ->
          define_or_replace_consed(DefineOrReplace, N, ReplacedRef0, Refmapping, ResultMapping0, LocalDefinitions0, RevGraph);
        false ->
          {ReplacedRef0, Refmapping, ResultMapping0, LocalDefinitions0#{ToDefineTy => DefineOrReplace}}
      end
  end.

-spec define_or_replace_consed(type(), type(), type(), #{temporary_ref() => type()}, #{type() => type_descriptor()}, #{type_descriptor() => type()}, #{type() => [type()]}) -> dar_acc().
define_or_replace_consed(ToDefine, N, ReplacedRef0, Refmapping, ResultMapping0, LocalDefinitions0, RevGraph) ->
  NodeContainedIn = ?assert_type(maps:get(ToDefine, RevGraph, []), [type()]),

  NewRefmapping = #{K => case V of ToDefine -> N; _ -> V end || K := V <- Refmapping},

  % remove ToDefine from result mapping, its already consed
  SmallerResultMapping = ?assert_type(maps:remove(ToDefine, ResultMapping0), #{type() => type_descriptor()}),

  FinalResultMapping = replace_in_rev_graph(ToDefine, N, SmallerResultMapping, NodeContainedIn),

  NewReplacedRef = case ReplacedRef0 of ToDefine -> N; _ -> ReplacedRef0 end,

  {NewReplacedRef, NewRefmapping, FinalResultMapping, LocalDefinitions0}.

-spec replace_in_rev_graph(type(), type(), #{type() => type_descriptor()}, [type()]) -> #{type() => type_descriptor()}.
replace_in_rev_graph(ToDefine, N, ResultMapping, NodeContainedIn) ->
  lists:foldl(fun(E, Acc0) ->
    case maps:find(E, Acc0) of
      error ->
        % E was already consed/removed in a prior step within this SCC
        Acc0;
      {ok, Val} ->
        dnf_ty_variable:assert_valid(Val),
        Fin = ?assert_type(utils:replace(Val, #{ToDefine => N}), type_descriptor()),
        FinalReordered = dnf_ty_variable:reorder(Fin),
        dnf_ty_variable:assert_valid(FinalReordered),
        Acc0#{E => FinalReordered}
    end
  end, ResultMapping, NodeContainedIn).

-spec is_not_defined(type(), type_descriptor()) -> boolean().
is_not_defined(Node, Rec) ->
  case ?assert_type(ets:lookup(ty_node_system, Node), [{type(), type_descriptor()}]) of
    [] -> true;
    [{Node, Rec}] -> false; % filter this FIXME how can a node be defined before with the same record???
    _ -> error(sanity) % this should not happen
  end.

-spec unparse_mapping(type()) -> {hit, ast_ty()} | no_hit.
unparse_mapping(Node) ->
  case ets:lookup(?UNPARSE_NAMED_MAPPING, Node) of
    [{Node, Res}] -> {hit, ?assert_type(Res, ast_ty())};
    _ -> no_hit
  end.

-spec is_consed(type_descriptor(), #{type_descriptor() => type()}) -> {true, type()} | false.
is_consed(ToDefineTy, LocalDefs) ->
  case ty_node:is_consed(ToDefineTy) of
    {true, Node} -> 
      {true, Node};
    _ ->
      case LocalDefs of
        #{ToDefineTy := Node} -> {true, Node};
        _ -> false
      end
  end.

-spec collect_refs(type(), #{type() => type_descriptor()}) -> [type()].
collect_refs(Ref, Results) ->
  Descriptor = maps:get(Ref, Results),
  ?assert_type(utils:everything(fun
    (E = {node, _}) -> {ok, E};
    (_) -> error
  end, Descriptor), [type()]).

% breadth-first traversal using a queue
% 
% it is not possible to use a depth-first approach with recursive types and the record data structure ty_rec
% see: T = {T U integer()}
% T is not yet defined when parsing the components of the tuple, 
% but it needs to be, because we need to load the value behind the reference
% while with breadth-first, we first parse T = {...},
% then T is defined, 
% then we can parse the inner components with the possibility of loading T inside {...}
-spec convert(queue(), database(), local_cache()) -> {database(), local_cache()}.
convert(Queue, Res, LocalCache) ->
  case queue:is_empty(Queue) of
    true -> 
      {Res, LocalCache}; 
    _ -> % convert next layer
      {{value, {LocalRef, Ty}}, Q} = ?assert_pattern({{value, {_, _}}, _}, queue:out(Queue)),
      % sanity: don't convert something that is already in the global system
      ?assert_pattern([], __Y, ets:lookup(?CACHE, LocalRef)),
      {ErlangRecOrLocalRef, NewQ, {R1, R2}, NewCache} = do_convert({Ty, Res}, Q, LocalCache),
      convert(NewQ, {R1#{LocalRef => ErlangRecOrLocalRef}, group(R2, ErlangRecOrLocalRef, LocalRef)}, NewCache)
  end.

% create an unique type reference
-spec new_local_ref() -> temporary_ref().
new_local_ref() -> {local_ref, erlang:unique_integer()}.

-spec new_local_ref(ast_ty()) -> temporary_ref().
new_local_ref(RawTerm) -> 
  % we want to lookup terms modulo LOC
  Term = replace_locs(RawTerm),
  % we could apply some simplifications here
  % &[A] = A
  % &[...,Empty,...] = Empty
  % etc
  % to map more terms to the same temporary reference
  % but this would likely only make random tests faster
  % semantic simplifications should happen in the internal representation,
  % not to make parsing faster

  % essentially, this is what we want but is too slow
  % {local_ref, Term}.
  % we can't use hashing, it is fast but leads to collisions
  % {local_ref, erlang:phash2(Term)}.
  % therefore, generate a unique reference and save in a hash table to lookup
  Reff = case ets:lookup(?TERMREFS, Term) of
    [{Term, Ref}] -> 
      ?assert_type(Ref, temporary_ref());
    _ -> 
      UniqueRef = new_local_ref(),
      ets:insert(?TERMREFS, {Term, UniqueRef}),
      UniqueRef
  end,
  % additionally, if that generated reference was unified at the last step,
  % we replace that generated reference with the unified reference,
  % to be able to hit the global cache 
  % (no unified discarded reference appears in the global cache)
  Final = case ets:lookup(?UNIFY, Reff) of
    [{Reff, UnifiedRef}] -> ?assert_type(UnifiedRef, temporary_ref());
    _ -> Reff 
  end,

  % this temporary reference has to behave exactly as a real node reference
  % when ordering inside a BDD
  % therefore, when comparing a temporary reference with a real reference
  % we have to already know to what the temporary reference would map to (in ty_node:compare/2)
  % therefore, we create a real reference beforehand and save it in the ty_parser state
  % whenever ty_node tries to compare a temporary reference against a real reference
  % ty_node has to look up the future mapping in ty_parser
  % create the future node mapping if not created already
  create_ref(Final),

  Final.

-spec extend_symtab(ast:ty_ref() | symtab:ty_key(), ety_ty_scheme()) -> _.
extend_symtab({_, Namespace, Type, ArgsCount}, RawTyScheme) ->
  Ref = {Namespace, Type, ArgsCount},
  % replace all locs 
  TyScheme = replace_locs(RawTyScheme),
  % io:format(user,"Extending symtab by ~p~n With scheme: ~p~n", [Ref, TyScheme]),
  ets:insert_new(?SYMTAB, {Ref, TyScheme}).

-spec lookup_ty(ast:ty_ref()) -> ety_ty_scheme().
lookup_ty({ty_qref, A, B, C}) ->
  Ref = {A, B, C},
  [{_, Scheme}] = ?assert_pattern([{_, _}], ets:lookup(?SYMTAB, Ref)),
  ?assert_type(Scheme, ety_ty_scheme());
lookup_ty({ty_ref, A, B, C}) ->
  Ref = {A, B, C},
  % io:format(user,"Lookup: ~p~nin~n~p~n", [Ref, ets:tab2list(?SYMTAB)]),
  [{_, Scheme}] = ?assert_pattern([{_, _}], ets:lookup(?SYMTAB, Ref)),
  ?assert_type(Scheme, ety_ty_scheme()).

-spec group(#{A => list(X)}, A, X) -> #{A => list(X)}.
group(M, Key, Value) ->
  case M of
    #{Key := Group} -> M#{Key => [Value | Group]};
    _ -> M#{Key => [Value]}
  end.

% entrypoint for recursion: named type
-spec do_convert({ast_ty(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert({X = {named, _, Ref, Args}, R}, Q, Cache) ->
  do_convert_named(X, Ref, Args, R, Q, Cache);
% fallthrough to mu/mu_var/predef types
do_convert(Arg, Q, Cache) -> do_convert_recursive(Arg, Q, Cache).

% dispatch for mu/mu_var/predef types
-spec do_convert_recursive({ast_ty_non_named(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_recursive({AstTy = {mu, RecVar = {mu_var, Name}, Ty}, R}, Q, Cache) ->
  do_convert_mu(AstTy, RecVar, Name, Ty, R, Q, Cache);
do_convert_recursive({AstTy = {mu_var, Name}, R}, Q, Cache) ->
  do_convert_mu_var(AstTy, Name, R, Q, Cache);
% fallthrough to predefined/simple types
do_convert_recursive(Arg, Q, Cache) -> do_convert_predef(Arg, Q, Cache).

% entrypoint for recursion: local equation
-spec do_convert_mu(ast:ty_mu(), ast:ty_mu_var(), ast:ty_varname(), ast:ty(), database(), queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_mu(AstTy, RecVar, Name, Ty, R, Q, Cache) ->
  ?assert_pattern(true, is_atom(Name)),

  NewRef = new_local_ref(AstTy),
  % all binders should be unique,
  % only binders with the same body are allowed to share the name
  % case maps:is_key(RecVar, Cache) of
  %   false -> ok;
  %   true -> ?assert_pattern(NewRef, maps:get(RecVar, Cache))
  % end,
  
  NewCache = Cache#{RecVar => NewRef},
  {InternalTy, NewQ, {R0, R1}, C0} = do_convert({Ty, R}, Q, NewCache),
  % return record
  {InternalTy, NewQ, {R0#{NewRef => InternalTy}, group(R1, InternalTy, NewRef)}, C0}.

% exit for recursion: local equation variable
-spec do_convert_mu_var(ast:ty_mu_var(), ast:ty_varname(), database(), queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_mu_var(AstTy, Name, R, Q, Cache) ->
  case is_atom(Name) of true -> true; _ -> error(exhaustiveness_violated) end,
  {IdTy, _} = R,

  Ref = case Cache of #{AstTy := R0} -> R0; _ -> error(exhaustiveness_violated) end,
  % We are allowed to load the memoized ref
  % because the second occurrence of the mu variable
  % is below a type constructor,
  % i.e. the memoized reference is fully defined
  Ty = case IdTy of #{Ref := T0} -> T0; _ -> error(exhaustiveness_violated) end,
  {Ty, Q, R, Cache}.

-spec do_convert_named(ast:ty_named(), ast:ty_ref(), ety_args(), database(), queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_named(X, Ref, Args, R = {IdTy, _}, Q, Cache) ->
  % add to create a reverse mapping between the internal result node and the named type
  case ets:lookup(?UNPARSE_NAMED_FINISHED, X) of
    [] -> ets:insert(?UNPARSE_NAMED_QUEUE, {X, []});
    _ -> ok % already processed
  end,

  case Cache of
    #{{Ref, Args} := CachedRef} ->
      Ty = case IdTy of #{CachedRef := T0} -> T0; _ -> error(exhaustiveness_violated) end,
      {Ty, Q, R, Cache};
    _ ->
      do_convert_named_new(X, Ref, Args, R, Q, Cache)
  end.

-spec do_convert_named_new(ast:ty_named(), ast:ty_ref(), ety_args(), database(), queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_named_new(X, Ref, Args, R, Q, Cache) ->
  % find ty in global table
  {ty_scheme, Vars, Ty} = lookup_ty(Ref),

  Map = subst:from_list(lists:zip([V || {V, _Bound} <- Vars], Args)),
  % we can do this since recursive variables should not descend "into" a named type
  NewTy = convert_back(debruijn(subst:apply(Map, Ty, no_clean))),

  % sanity (commented out: causes type check complexity)
  ?assert_pattern(false, maps:is_key({Ref, Args}, Cache)),

  NewRef = new_local_ref(X),
  case ets:lookup(?CACHE, NewRef) of
    [] ->
      % create a new reference (ref args pair), memoize, and add continue converting
      {InternalTy, NewQ, {R0, R1}, C0} = do_convert({NewTy, R}, Q, Cache#{{Ref, Args} => NewRef}),
      {InternalTy, NewQ, {R0#{NewRef => InternalTy}, group(R1, InternalTy, NewRef)}, C0};
    [{NewRef, CachedNode}] ->
      % reuse type representation of the global cache
      InternalTy = ?NODE:load(?assert_type(CachedNode, ty_node:type())),
      {InternalTy, Q, R, Cache};
    _ -> 
      convert_error({unexpected_cache_result, NewRef})
  end.

% built-ins and predefined types
-spec do_convert_predef({ast_ty_predef(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_predef({{predef, X}, R}, Q, Cache) -> do_convert_predef_atom(X, R, Q, Cache);
do_convert_predef({{predef_alias, Alias}, R}, Q, Cache) -> do_convert({stdtypes:expand_predef_alias(Alias), R}, Q, Cache);
% fallthrough to builtins and literals
do_convert_predef(Arg, Q, Cache) -> do_convert_builtin(Arg, Q, Cache).

-spec do_convert_predef_atom(ast:predef_name(), database(), queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_predef_atom(dynamic, R, Q, Cache) -> {?TY:singleton(ty_variable:new_as_frame()), Q, R, Cache};
do_convert_predef_atom(any, R, Q, Cache) -> {?TY:any(), Q, R, Cache};
do_convert_predef_atom(none, R, Q, Cache) -> {?TY:empty(), Q, R, Cache};
do_convert_predef_atom(atom, R, Q, Cache) -> {?TY:atom(dnf_ty_atom:any()), Q, R, Cache};
do_convert_predef_atom(integer, R, Q, Cache) -> {?TY:interval(dnf_ty_interval:any()), Q, R, Cache};
do_convert_predef_atom(T, R, Q, Cache) when T == pid; T == port; T == reference; T == float ->
  {?TY:predefined(dnf_ty_predefined:predefined(T)), Q, R, Cache}.

% predefined builtins
-type ast_ty_builtin() :: ast:ty_singleton() | ast:ty_bitstring() | ast:ty_some_list()
    | ast:ty_fun() | ast:ty_integer_range() | ast:ty_map_any() | ast:ty_map()
    | ast:ty_tuple_any() | ast:ty_tuple() | ast:ty_var()
    | ast:ty_union() | ast:ty_intersection() | ast:ty_negation().
-spec do_convert_builtin({ast_ty_builtin(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_builtin({{fun_simple}, R}, Q, Cache) -> {?TY:functions(ty_functions:any()), Q, R, Cache};
do_convert_builtin({{tuple_any}, R}, Q, Cache) -> {?TY:tuples(ty_tuples:any()), Q, R, Cache};
do_convert_builtin({{empty_list}, R}, Q, Cache) -> {?TY:predefined(dnf_ty_predefined:predefined('[]')), Q, R, Cache};
do_convert_builtin({{map_any}, R}, Q, Cache) ->
  {?TY:map(dnf_ty_map:any()), Q, R, Cache};
do_convert_builtin({{fun_any_arg, _} = T, _R}, _Q, _Cache) ->
  convert_error(T);
% fallthrough to literals
do_convert_builtin(Arg, Q, Cache) -> do_convert_literal(Arg, Q, Cache).

% bitstrings, singletons, ranges
-type ast_ty_literal() :: ast:ty_singleton() | ast:ty_bitstring()
    | ast:ty_cons() | ast:ty_list() | ast:ty_nonempty_list()
    | ast:ty_improper_list() | ast:ty_nonempty_improper_list()
    | ast:ty_full_fun()
    | ast:ty_integer_range() | ast:ty_map() | ast:ty_tuple() | ast:ty_var()
    | ast:ty_union() | ast:ty_intersection() | ast:ty_negation().
-spec do_convert_literal({ast_ty_literal(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_literal({{bitstring}, R}, Q, Cache) ->
  {?TY:bitstring(dnf_ty_bitstring:any()), Q, R, Cache};
do_convert_literal({{bitstring, M, N}, R}, Q, Cache) ->
  {?TY:bitstring(dnf_ty_bitstring:from_m_n(M, N)), Q, R, Cache};
do_convert_literal({{singleton, Atom}, R}, Q, Cache) when is_atom(Atom) ->
  TAtom = dnf_ty_atom:finite([Atom]),
  {?TY:atom(TAtom), Q, R, Cache};
do_convert_literal({{singleton, I}, R}, Q, Cache) when is_integer(I) ->
  Int = dnf_ty_interval:interval(I, I),
  {?TY:interval(Int), Q, R, Cache};
do_convert_literal({{range, From, To}, R}, Q, Cache) ->
  Int = dnf_ty_interval:interval(From, To),
  {?TY:interval(Int), Q, R, Cache};
% fallthrough to compound types
do_convert_literal(Arg, Q, Cache) -> do_convert_compound(Arg, Q, Cache).

% boolean operators: dispatch to specialized helpers
-spec do_convert_compound({ast_ty_compound(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_compound({{union, L}, R}, Q, Cache) -> do_convert_union(L, R, Q, Cache);
do_convert_compound({{intersection, L}, R}, Q, Cache) -> do_convert_intersect(L, R, Q, Cache);
do_convert_compound({{negation, Ty}, R}, Q, Cache) ->
  {NewR, Q0, RR0, C0} = do_convert({Ty, R}, Q, Cache),
  {?TY:negate(NewR), Q0, RR0, C0};
% fallthrough to rewrites and data types
do_convert_compound(Arg, Q, Cache) -> do_convert_rewrite(Arg, Q, Cache).

-spec do_convert_union([ast_ty()], database(), queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_union([], R, Q, Cache) -> {?TY:empty(), Q, R, Cache};
do_convert_union([A], R, Q, Cache) -> do_convert({A, R}, Q, Cache);
do_convert_union([A|T], R, Q, Cache) ->
  {R1, Q1, RR1, C1} = do_convert({A, R}, Q, Cache),
  {R2, Q2, RR2, C2} = do_convert({{union, T}, RR1}, Q1, C1),
  {?TY:union(R1, R2), Q2, RR2, C2}.

-spec do_convert_intersect([ast_ty()], database(), queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_intersect([], R, Q, Cache) -> {?TY:any(), Q, R, Cache};
do_convert_intersect([A], R, Q, Cache) -> do_convert({A, R}, Q, Cache);
do_convert_intersect([A|T], R, Q, Cache) ->
  {R1, Q1, RR0, C0} = do_convert({A, R}, Q, Cache),
  {R2, Q2, RR1, C1} = do_convert({{intersection, T}, RR0}, Q1, C0),
  {?TY:intersect(R1, R2), Q2, RR1, C1}.

% variables and term rewrites
-spec do_convert_rewrite({ast_ty_rewrite(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
% variables
do_convert_rewrite({{var, A}, R}, Q, Cache) ->
  % if this is a special $ety_integer()_name() variable, convert to that representation
  case string:prefix(atom_to_list(A), "$ety_") of
    nomatch ->
      {?TY:singleton(ty_variable:new_with_name(A)), Q, R, Cache};
    IdName ->
      % TODO test case for this branch
      % assumption: erlang types generates variables only in this pattern: $ety_integer()_name()
      [Id, Name] = ?assert_pattern([_,_], string:split(?assert_type(IdName, string()), "_")),
      {?TY:singleton(ty_variable:with_name_and_id(list_to_integer(Id), list_to_atom(Name))), Q, R, Cache}
  end;
% fallthrough to list rewrites, map, and data structure types
do_convert_rewrite(Arg, Q, Cache) -> do_convert_rewrite_list(Arg, Q, Cache).

% === term rewrites
-spec do_convert_rewrite_list({ast_ty_rewrite_list(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert_rewrite_list({{nonempty_list, Ty}, R}, Q, Cache) ->
  do_convert({{cons, Ty, {list, Ty}} , R}, Q, Cache);
do_convert_rewrite_list({{nonempty_improper_list, Ty, Term}, R}, Q, Cache) ->
  do_convert({{cons, Ty, {improper_list, Ty, Term}} , R}, Q, Cache);
do_convert_rewrite_list({{list, Ty}, R}, Q, Cache) ->
  do_convert({{improper_list, Ty, {empty_list}}, R}, Q, Cache);
% fallthrough to map and data structure types
do_convert_rewrite_list(Arg, Q, Cache) -> do_convert_rewrite_map(Arg, Q, Cache).

-spec do_convert_rewrite_map({ast_ty_rewrite_map(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
% rewrite maps into {Tuple, Function} tuples
do_convert_rewrite_map({M = {map, _}, R}, Q, Cache) ->
  MapTuple = rewrite_map_to_representation(M),
  {Recc, Q0, R0, C0} = do_convert({MapTuple, R}, Q, Cache),
  {?TY:tuple_to_map(?assert_type(Recc, dnf_ty_variable:leaf())), Q0, R0, C0};
% fallthrough to data structure types
do_convert_rewrite_map(Arg, Q, Cache) -> do_convert_data(Arg, Q, Cache).

% data structure types: functions, tuples, lists
-spec do_convert_data({ast_ty_data(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
% functions
do_convert_data({{fun_full, Domains, CoDomain}, R}, Q, Cache) ->
  {ParsedDomains, Q0} = queue_all(Domains, Q),
  {ParsedCoDomain, Q1} = queue_if_new(CoDomain, Q0),

  T = ty_functions:singleton(length(Domains), dnf_ty_function:singleton(ty_function:function(
    ?assert_type(ParsedDomains, [ty_node:type()]), ?assert_type(ParsedCoDomain, ty_node:type())))),
  {?TY:functions(T), Q1, R, Cache};

% tuples
do_convert_data({{tuple, Comps}, R}, Q, Cache) ->
  {ParsedComponents, Q0} = queue_all(Comps, Q),

  T = ty_tuples:singleton(length(Comps), dnf_ty_tuple:singleton(ty_tuple:tuple(
    ?assert_type(ParsedComponents, [ty_node:type()])))),
  {?TY:tuples(T), Q0, R, Cache};

% lists
do_convert_data({{improper_list, A, B}, R}, Q, Cache) ->
  RVar = {mu_var, list_to_atom(integer_to_list(erlang:unique_integer()))},
  NewTerm = {mu, RVar, {union, [B, {cons, A, RVar}]}},
  do_convert({NewTerm, R}, Q, Cache);
do_convert_data({{cons, A, B}, R}, Q, Cache) ->
  {T1, Q0} = queue_if_new(A, Q),
  {T2, Q1} = queue_if_new(B, Q0),

  {?TY:list(dnf_ty_list:singleton(ty_list:list([?assert_type(T1, ty_node:type()), ?assert_type(T2, ty_node:type())]))), Q1, R, Cache}.

-spec queue_all([ast_ty()], queue()) -> {[type() | temporary_ref()], queue()}.
queue_all(Elements, Q) ->
  lists:foldl(
    fun(Element, {Components, OldQ}) ->
      {IdOrNode, QQ} = queue_if_new(Element, OldQ),
      {Components ++ [IdOrNode], QQ}
    end, {[], Q}, Elements).

-spec queue_if_new(ast_ty(), queue()) -> {type() | temporary_ref(), queue()}.
queue_if_new(Element, Queue) ->
  Id = new_local_ref(Element),
  case ets:lookup(?CACHE, Id) of
    % to be converted later, add to queue, return temporary reference
    [] -> 
      {Id, queue:in({Id, Element}, Queue)};
    % if already known, don't process and return a real reference
    [{Id, Node}] -> 
      {?assert_type(Node, type()), Queue};
    _ -> 
      error(invariant)
  end.

-spec unify(temporary_ref(), database()) -> {temporary_ref(), #{temporary_ref() => ty_rec()}}.
unify(Ref, {IdToTy, TyToIds}) ->
  % map with references to unify, pick representatives
  % in previous versions, named_ref existed, which was picked preferrably as the representative
  % now, we pick the first element
  ToUnify = maps:to_list(#{
    K => 
      begin 
        % we can't forget the references which are unified to another reference
        % when we create a new_local_reference, 
        % if that is mapped to a reference which was unified before 
        % that missed reference will not be cached, even though the converting work has been done before already
        % therefore, add all unified reference to a separate cache
        % and check whenever we create a local reference that unify cache
        lists:foreach(fun(E) -> ?assert_pattern(true, ets:insert_new(?UNIFY, {E, H})) end, T),
        {H, T} 
      end
    || K := (V = [H | T]) <- TyToIds, length(V) > 1}), 

  % replace equivalent refs with representative
  ToReplace = maps:from_list(lists:flatten([[{Single, Represent} || Single <- Dupl ] || {_, {Represent, Dupl}}<- ToUnify])),
  utils:replace({Ref, IdToTy}, ToReplace).

-spec unparse(type()) -> ast_ty().
unparse(Node) ->
  Z = case ets:lookup(?UNPARSE_CACHE, Node) of
    [{_, Ref}] -> 
      ?assert_type(persistent_term:get(Ref), ast_ty());
    _ ->
      {R, _} = ty_node:unparse(Node, #{}),

      Ref = make_ref(),
      persistent_term:put(Ref, R),
      % inserting R into ets (as a value) is extremely slow if R is a big term
      ?assert_pattern(true, ets:insert_new(?UNPARSE_CACHE, {Node, Ref})),
      
      R
  end,
  Z.


-spec debruijn(ast_ty()) -> ast_ty().
debruijn(Type) ->
  debruijn(Type, []).

-type var_env() :: [ast:ty_varname()].
%% helper with variable name environment stack
-spec debruijn(ast_ty(), var_env()) -> ast_ty().
% local recursion
debruijn({mu, {mu_var, Name}, Body}, Env) ->
  NewEnv = [Name | Env],
  {mu, {mu_var, nameless}, debruijn(Body, NewEnv)}; % add mu_var anyway to still be a ast_ty()
debruijn({mu_var, Name}, Env) ->
  case index_of(Name, Env) of
    {ok, Index} -> {mu_var, list_to_atom(integer_to_list(Index))};
    not_found -> error({unbound_variable, Name})
  end;
debruijn(Type, Env) -> debruijn_1(Type, Env).

-spec debruijn_1(ast_ty_db1(), var_env()) -> ast_ty().
debruijn_1({singleton, _} = T, _Env) -> T;
debruijn_1({bitstring}, _Env) -> {bitstring};
debruijn_1({bitstring, M, N}, _Env) -> {bitstring, M, N};
debruijn_1({empty_list}, _Env) -> {empty_list};
debruijn_1({cons, U, L}, Env) -> {cons, debruijn(U, Env), debruijn(L, Env)};
debruijn_1({list, U}, Env) -> {list, debruijn(U, Env)};
debruijn_1(Type, Env) -> debruijn_2(Type, Env).

-spec debruijn_2(ast_ty_db2(), var_env()) -> ast_ty().
debruijn_2({nonempty_list, U}, Env) -> {nonempty_list, debruijn(U, Env)};
debruijn_2({improper_list, U, V}, Env) ->
  {improper_list, debruijn(U, Env), debruijn(V, Env)};
debruijn_2({nonempty_improper_list, U, V}, Env) ->
  {nonempty_improper_list, debruijn(U, Env), debruijn(V, Env)};
debruijn_2({fun_simple}, _Env) -> {fun_simple};
debruijn_2({fun_any_arg, U}, Env) -> {fun_any_arg, debruijn(U, Env)};
debruijn_2({fun_full, Args, U}, Env) ->
  {fun_full, debruijn_list(Args, Env), debruijn(U, Env)};
debruijn_2(Type, Env) -> debruijn_3(Type, Env).

-spec debruijn_3(ast_ty_db3(), var_env()) -> ast_ty().
debruijn_3({range, Min, Max}, _Env) -> {range, Min, Max};
debruijn_3({map_any}, _Env) -> {map_any};
debruijn_3({map, Assocs}, Env) ->
  {map, lists:map(fun({Kind, U, V}) ->
    {Kind, debruijn(U, Env), debruijn(V, Env)}
  end, Assocs)};
debruijn_3({predef, Name}, _Env) -> {predef, Name};
debruijn_3({predef_alias, Name}, _Env) -> {predef_alias, Name};
debruijn_3({named, Loc, Ref, Args}, Env) ->
  {named, Loc, Ref, debruijn_list(Args, Env)};
debruijn_3(Type, Env) -> debruijn_4(Type, Env).

-spec debruijn_4(ast_ty_db4(), var_env()) -> ast_ty().
debruijn_4({tuple_any}, _Env) -> {tuple_any};
debruijn_4({tuple, Args}, Env) -> {tuple, debruijn_list(Args, Env)};
debruijn_4({var, Alpha}, _Env) -> {var, Alpha};
debruijn_4({union, Args}, Env) -> {union, debruijn_list(Args, Env)};
debruijn_4({intersection, Args}, Env) -> {intersection, debruijn_list(Args, Env)};
debruijn_4({negation, U}, Env) -> {negation, debruijn(U, Env)}.

%% Helper to debruijn lists of types

-spec debruijn_list([ast_ty()], var_env()) -> [ast_ty()].
debruijn_list(Types, Env) ->
  [debruijn(T, Env) || T <- Types].

%% Helper to find the index of a name in the environment
-spec index_of(ast:ty_varname(), var_env()) -> {ok, non_neg_integer()} | not_found.
index_of(Name, Env) ->
  index_of(Name, Env, 0).

-spec index_of(ast:ty_varname(), var_env(), non_neg_integer()) -> {ok, non_neg_integer()} | not_found.
index_of(Name, [Name|_], Index) -> {ok, Index};
index_of(Name, [_|Rest], Index) -> index_of(Name, Rest, Index + 1);
index_of(_, [], _) -> not_found.


%% Conversion back to named variables with fresh names
-spec convert_back(ast_ty()) -> ast_ty().
convert_back(Type) ->
  {Result, _} = convert_back(Type, [], 0),
  Result.

-spec convert_back(ast_ty(), var_env(), non_neg_integer()) -> {ast_ty(), non_neg_integer()}.
convert_back({mu, _, Body}, Env, Counter) ->
  Name = make_fresh_name(Counter),
  NewEnv = [Name | Env],
  {ConvertedBody, NewCounter} = convert_back(Body, NewEnv, Counter + 1),
  {{mu, {mu_var, Name}, ConvertedBody}, NewCounter};
convert_back({mu_var, Index}, Env, Counter) ->
  Name = lists:nth(?assert_type(list_to_integer(atom_to_list(Index)) + 1, pos_integer()), ?assert_type(Env, [ast:ty_varname(), ...])),
  {{mu_var, Name}, Counter};
convert_back({var, Name}, _Env, Counter) ->
  {{var, Name}, Counter};
convert_back({tuple, Args}, Env, Counter) ->
  {ConvertedArgs, NewCounter} = convert_back_list(Args, Env, Counter),
  {{tuple, ConvertedArgs}, NewCounter};
convert_back({union, Args}, Env, Counter) ->
  {ConvertedArgs, NewCounter} = convert_back_list(Args, Env, Counter),
  {{union, ConvertedArgs}, NewCounter};
convert_back({intersection, Args}, Env, Counter) ->
  {ConvertedArgs, NewCounter} = convert_back_list(Args, Env, Counter),
  {{intersection, ConvertedArgs}, NewCounter};
%% Handle all other type constructors similarly
convert_back(Type, Env, Counter) ->
  convert_back_other(Type, Env, Counter).

-spec convert_back_other(ast_ty_cb_other(), var_env(), non_neg_integer()) -> {ast_ty(), non_neg_integer()}.
convert_back_other({list, Arg}, Env, Counter) ->
  {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
  {{list, ConvertedArg}, NewCounter};
convert_back_other({nonempty_list, Arg}, Env, Counter) ->
  {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
  {{nonempty_list, ConvertedArg}, NewCounter};
convert_back_other({cons, Arg, Arg2}, Env, Counter) ->
  {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
  {ConvertedArg2, NewCounter2} = convert_back(Arg2, Env, NewCounter),
  {{cons, ConvertedArg, ConvertedArg2}, NewCounter2};
convert_back_other({improper_list, Arg, Arg2}, Env, Counter) ->
  {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
  {ConvertedArg2, NewCounter2} = convert_back(Arg2, Env, NewCounter),
  {{improper_list, ConvertedArg, ConvertedArg2}, NewCounter2};
convert_back_other({nonempty_improper_list, Arg, Arg2}, Env, Counter) ->
  {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
  {ConvertedArg2, NewCounter2} = convert_back(Arg2, Env, NewCounter),
  {{nonempty_improper_list, ConvertedArg, ConvertedArg2}, NewCounter2};
convert_back_other(Type, Env, Counter) ->
  convert_back_rest(Type, Env, Counter).

-spec convert_back_rest(ast_ty_cb_rest(), var_env(), non_neg_integer()) -> {ast_ty(), non_neg_integer()}.
convert_back_rest({fun_any_arg, Arg}, Env, Counter) ->
  {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
  {{fun_any_arg, ConvertedArg}, NewCounter};
convert_back_rest({negation, Arg}, Env, Counter) ->
  {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
  {{negation, ConvertedArg}, NewCounter};
convert_back_rest({fun_full, Args, Ret}, Env, Counter) ->
  {ConvertedArgs, Counter1} = convert_back_list(Args, Env, Counter),
  {ConvertedRet, NewCounter} = convert_back(Ret, Env, Counter1),
  {{fun_full, ConvertedArgs, ConvertedRet}, NewCounter};
convert_back_rest({map, Assocs}, Env, Counter) ->
  {ConvertedAssocs, NewCounter} = convert_back_assocs(Assocs, Env, Counter),
  {{map, ConvertedAssocs}, NewCounter};
convert_back_rest({named, Loc, Ref, Args}, Env, Counter) ->
  {ConvertedArgs, NewCounter} = convert_back_list(Args, Env, Counter),
  {{named, Loc, Ref, ConvertedArgs}, NewCounter};
convert_back_rest(Type, _Env, Counter) ->
  {Type, Counter}.

-spec convert_back_list([ast_ty()], var_env(), non_neg_integer()) -> {[ast_ty()], non_neg_integer()}.
convert_back_list([], _Env, Counter) -> {[], Counter};
convert_back_list([Type|Rest], Env, Counter) ->
  {Converted, Counter1} = convert_back(Type, Env, Counter),
  {ConvertedRest, NewCounter} = convert_back_list(Rest, Env, Counter1),
  {[Converted|ConvertedRest], NewCounter}.

-spec convert_back_assocs([ast:ty_map_assoc()], var_env(), non_neg_integer()) -> {[ast:ty_map_assoc()], non_neg_integer()}.
convert_back_assocs([], _, Counter) -> {[], Counter};
convert_back_assocs([{Kind, K, V}|Rest], Env, Counter) ->
  {ConvertedK, Counter1} = convert_back(K, Env, Counter),
  {ConvertedV, Counter2} = convert_back(V, Env, Counter1),
  {ConvertedRest, NewCounter} = convert_back_assocs(Rest, Env, Counter2),
  {[{Kind, ConvertedK, ConvertedV}|ConvertedRest], NewCounter}.

-spec make_fresh_name(non_neg_integer()) -> ast:ty_varname().
make_fresh_name(Counter) ->
  list_to_atom("$var_" ++ integer_to_list(Counter)).

-spec assert_replaced_refs_have_good_order(#{temporary_ref() => type()}) -> ok.
assert_replaced_refs_have_good_order(Refs) ->
  validate_map(Refs),
  ok.

-spec validate_map(#{temporary_ref() => type()}) -> boolean().
validate_map(Map) ->
  Pairs = lists:keysort(1, maps:to_list(Map)),
  check_pairs(Pairs).

-spec check_pairs([{temporary_ref(), type()}]) -> boolean().
check_pairs([]) -> true;
check_pairs([_]) -> true;
check_pairs([{K1, {node, N1}}, {K2, {node, N2}} | Rest]) ->
  case K1 < K2 of
    true when N1 < N2 -> check_pairs([{K2, {node, N2}} | Rest]);
    true -> false;  % K1 < K2 but N1 >= N2
    false -> check_pairs([{K2, {node, N2}} | Rest])  % K1 >= K2, no requirement
  end.

-spec replace_locs
  (ety_ty_scheme()) -> ety_ty_scheme();
  (ast_ty()) -> ast_ty().
replace_locs(Term) ->
  utils:everywhere(fun
    ({loc, _, _, _}) -> {ok, {loc, "AUTO", -1, -1}};
    (_) -> error 
  end, Term).

-spec convert_error(term()) -> no_return().
convert_error(T) ->
  erlang:error({"Transformation from ast:ty() to ty_rec:ty() not implemented or malformed type", T}).

-spec rewrite_map_to_representation(ast:ty_map()) -> ast_ty().
rewrite_map_to_representation({map, AssocList}) ->
  {_, TupPart, FunPart} = rewrite_map_fold(AssocList),
  {tuple, [TupPart, FunPart]}.

-spec rewrite_map_fold([ast:ty_map_assoc()]) -> {ast_ty(), ast_ty(), ast_ty()}.
rewrite_map_fold(AssocList) ->
  lists:foldl(
    fun(Assoc, Acc) -> rewrite_map_assoc(Assoc, Acc) end,
    % a map type is never empty
    % contrary to tuples, we can construct an empty map value: #{}
    % since empty tuples are the empty type, we add an atom 'empty_map' to the tuple part
    % so that the encoding is never empty
    {{predef, none}, {singleton, empty_map}, {fun_simple}}, AssocList).

-spec rewrite_map_assoc(ast:ty_map_assoc(), {ast_ty(), ast_ty(), ast_ty()}) -> {ast_ty(), ast_ty(), ast_ty()}.
rewrite_map_assoc({Association, Key, Val}, {PrecedenceDomain, Tuples, Functions}) ->
  Tup = {tuple, [{intersection, [Key, {negation, PrecedenceDomain}]}, Val]},
  NewDomain = {union, [PrecedenceDomain, Key]},
  NewTuples = {union, [Tuples, Tup]},
  case Association of
    map_field_opt ->
      {NewDomain, NewTuples, Functions};
    map_field_req ->
      Fun = {fun_full, [{intersection, [Key, {negation, PrecedenceDomain}]}], Val},
      {NewDomain, NewTuples, {intersection, [Functions, Fun]}}
  end.
