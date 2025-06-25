-module(ty_parser).

-compile([export_all, nowarn_export_all]).

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

% a cache of discarded references which disappear after unification
% used to re-map local references to the unified reference, if possible
-define(UNIFY, ty_parser_unify).

% cache for unparsing nodes
-define(UNPARSE_CACHE, ty_parser_unparse_cache).

% mapping from node -> named used in unparsing
% this is a bit of a hack;
% during conversion, save all encountered {named, ...} types
% after conversion, convert them (which have not yet been converted yet) one by one again and save that reverse mapping
-define(UNPARSE_NAMED_MAPPING, ty_parser_unparse_name_cache).
-define(UNPARSE_NAMED_QUEUE, ty_parser_unparse_queue).
-define(UNPARSE_NAMED_FINISHED, ty_parser_unparse_finish).

-define(ALL_ETS, [?CACHE, ?SYMTAB, ?TERMREFS, ?UNIFY, ?UNPARSE_CACHE, ?UNPARSE_NAMED_QUEUE, ?UNPARSE_NAMED_FINISHED, ?UNPARSE_NAMED_MAPPING]).

-define(TY, dnf_ty_variable).
-define(NODE, ty_node).

-type temporary_ref() :: {local_ref, integer()}. % type references created for the queue
-type type() :: ?NODE:type().
-type ty_rec() :: ?TY:type().
-type ast_ty() :: term(). %TODO ast:ty()
-type ety_ty_scheme() :: term(). %TODO etylizer ty scheme
-type ety_ref() :: term(). %TODO etylizer reference
-type ety_args() :: term(). %TODO [ast:ty()]
-type database() :: {term(), term()}. 
-type local_cache() :: {{Ref :: ety_ref(), Args :: ety_args()}, temporary_ref()}. % the local cache should only consist of temporary references
-type queue() :: queue:queue({temporary_ref(), ast_ty()}).

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

-spec parse(ast_ty()) -> type().
parse(RawTy) ->
  % first: rename such that mu-binders have no collisions
  % use DeBruijn indexes and then convert back to fresh named variables
  % this has to be done anytime a {named, ...} reference is unfolded, too
  Ty = convert_back(debruijn(RawTy)),

  % create a reference, check if it is inside the cache
  LocalRef = new_local_ref(Ty),

  FinalResult = 
  case ets:lookup(?CACHE, LocalRef) of
    [{LocalRef, Node}] -> 
      Node;
    _ ->
      % 1. Convert to temporary local representation
      %    Create a temporary type equation with a first entrypoint LocalRef = ...
      %    and parse the type layer by layer
      %    use local type references stored in a local map
      ({{NewR, NewTUnsorted}, _NewCache}) = convert(queue:from_list([{LocalRef, Ty}]), {_RefToTy = #{}, _TyToRef = #{}}, #{}),
      % can have duplicates, e.g. TODO explain
      NewT = #{K => lists:usort(V) || K := V <- NewTUnsorted},
      % io:format(user,"Result of Converting:~n~p~n~p~n", [NewR, NewT]),

      % 2. (Locally) unify the results
      %    There can be many duplicate type references;
      %    these will be substituted with their representative
      %    e.g. any U any    any          type to parse
      %         ref1         ref2         local temporary references
      %         internal1    internal1    internal type representations
      %    replace all ref2 by ref1, so that no unecessary nodes are created
      {UnifiedRef, UnifiedResult} = unify(LocalRef, {NewR, NewT}),
      % io:format(user,"Unified:~n~p~n", [UnifiedResult]),

      % 3. create new type references and replace temporary ones
      %    return result reference
      ReplaceRefs = maps:from_list([{Ref, ?NODE:new_ty_node()} || Ref <- maps:keys(UnifiedResult)]),
      {ReplacedRef, ReplacedResults} = utils:replace({UnifiedRef, UnifiedResult}, ReplaceRefs),
      % io:format(user,"Replaced:~n~p~n", [ReplacedResults]),

      % 4. define types
      % 4.1 create a graph, a reverse graph, a condensed graph, then topological sort, then define and replace if already consed
      Graph = #{K => lists:usort(V) || K := V <- #{Ref => collect_refs(Ref, ReplacedResults) || Ref := _ <- ReplacedResults}},
      RevGraph = utils:reverse_graph(Graph),

      {Scc, Condensed} = utils:condense(Graph),

      Components = lists:foldl(fun({Node, Root}, Acc) ->
        maps:update_with(Root, fun(Nodes) -> [Node | Nodes] end, [Node], Acc)
      end, #{}, maps:to_list(Scc)),

      Sort = utils:dfs(Condensed),
      Define = [maps:get(T, Components) || T <- Sort],


      DefineAndReplace = fun({{ReplacedRef1, RefMapping, ResultMapping, LocalDefinitions}, Def, Rest}) -> 
        {NewReplacedRef, NewRef, NewRes, NewLocalDefinitions, NewRest} = lists:foldl(fun(DefineOrReplace, Acc = {ReplacedRef0, Refmapping, ResultMapping0, LocalDefinitions0, Rest0}) ->
          case ?NODE:is_defined(DefineOrReplace) of
            true -> % from previous parsing runs
              Acc;
            false ->
              ToDefineTy = maps:get(DefineOrReplace, ResultMapping0),
              case is_consed(ToDefineTy, LocalDefinitions0) of
                {true, N} -> 
                  ToDefine = DefineOrReplace,

                  NodeContainedIn = maps:get(ToDefine, RevGraph, []),

                  NewRefmapping = #{K => case V of ToDefine -> N; _ -> V end || K := V <- Refmapping},

                  % remove ToDefine from result mapping, its already consed
                  SmallerResultMapping = maps:remove(ToDefine, ResultMapping0),

                  FinalResultMapping = lists:foldl(fun(E, Acc0) -> 
                    Val = maps:get(E, Acc0),
                    Fin = utils:replace(Val, #{ToDefine => N}),
                    Acc0#{E => Fin} 
                  end, SmallerResultMapping, NodeContainedIn),

                  NewReplacedRef = case ReplacedRef0 of ToDefine -> N; _ -> ReplacedRef0 end,

                  {NewReplacedRef, NewRefmapping, FinalResultMapping, LocalDefinitions0, Rest0};
                false ->
                  % so this can happen with recursive types:
                  % the ty_rec is already consed,
                  % but the reference has been used already in a previous definition.
                  % Ideally, we don't want to define this reference.
                  % But we need to, since this reference is used in another definition already (in this local parse)
                  % We don't want to touch anything that has been defined already (globally),
                  % so we need to prevent this case from happening in the first place.
                  % The problem is that local unification is not smart enough to merge these two type references in one pass:
                  % 
                  % {local_ref,-576460752303423167} => ... {ty_function, [{local_ref,-576460752303423071}], {local_ref,-576460752303423231}} ...
                  % {local_ref,-576460752303423135} => ... {ty_function, [{local_ref,-576460752303423071}], {local_ref,-576460752303423231}} ...
                  % 
                  % Which (before and) after replacement point to the same records
                  % 
                  % {node,3} => ... {ty_function,[{node,6}],{node,1}} ...
                  % {node,4} => ... {ty_function,[{node,6}],{node,1}} ...
                  % 
                  % Therefore, we don't define the types globally, but locally first
                  % and remove the duplicates once a consed match is detected
                  {ReplacedRef0, Refmapping, ResultMapping0, LocalDefinitions0#{ToDefineTy => DefineOrReplace}, Rest0}
              end
            end
          end, {ReplacedRef1, RefMapping, ResultMapping, LocalDefinitions, Rest}, Def),

      {{NewReplacedRef, NewRef, NewRes, NewLocalDefinitions}, NewRest}
    end,

    % Modifying the context is not needed
    % TODO refactor
    {FinalReplacedRef, FinalReplaceRefs, FinalReplacedResults, _FinalLocalDefinitions} = utils:fold_with_context(DefineAndReplace, {ReplacedRef, ReplaceRefs, ReplacedResults, _LocalDefinitions = #{}}, Define),

    % define the final results globally
    [?NODE:define(NodeRef, Record) || NodeRef := Record <- FinalReplacedResults],

    % 5. update global cache, there are now old entries to overwrite
    %    this invariant has to be kept up inside do_convert
    %    whenever a new reference is created with new_local_ref(...),
    %    we need to check the global cache if that reference does not already point
    %    to a real node inside the global system
    %    the true = ... check is a sanity check
    %    if somethings has been inserted before, it had to be Node already
    [case ets:insert_new(?CACHE, {LLocalRef, Node}) of
       true -> ok;
       false -> [{LLocalRef, Node}] = ets:lookup(?CACHE, LLocalRef), ok
     end
     || LLocalRef := Node <- FinalReplaceRefs],

    % sanity check: all references should be defined
    % [ty_node:dump(Node) || _LLocalRef := Node <- FinalReplaceRefs],
      
    FinalReplacedRef
  end,
  
  % generate the reverse named mapping at the end
  InQueue = ets:tab2list(?UNPARSE_NAMED_QUEUE),
  lists:foreach(
    fun({N, _}) -> 
      case ets:lookup(?UNPARSE_NAMED_FINISHED, N) of 
        [] -> 
          ets:insert(?UNPARSE_NAMED_FINISHED, {N, []}),
          ets:delete(?UNPARSE_NAMED_QUEUE, N),
          Mapping = parse(N),
          case ets:insert_new(?UNPARSE_NAMED_MAPPING, {Mapping, N}) of
            true -> 
              % io:format(user, "Created reverse mapping for ~w :: ~w~n", [Mapping, N]),
              ok;
            _ -> 
              % [{Mapping, OldNode}] = ets:lookup(?UNPARSE_NAMED_MAPPING, Mapping), 
              % io:format(user, "Warning: ~p maps to a node that already has a reverse mapping:~n~p~n", [N, OldNode]),
              ok
          end;
        _ -> ok 
      end 
    end, InQueue),
  
  FinalResult.

unparse_mapping(Node) ->
  case ets:lookup(?UNPARSE_NAMED_MAPPING, Node) of
    [{Node, Res}] -> {hit, Res};
    _ -> no_hit
  end.

is_consed(ToDefineTy, LocalDefs) ->
  case ?NODE:is_consed(ToDefineTy) of
    {true, N} -> {true, N};
    _ ->
      case LocalDefs of
        #{ToDefineTy := Rec} -> {true, Rec};
        _ -> false
      end
  end.

collect_refs(Ref, Results) ->
  utils:everything(fun
    (E = {node, _}) -> {ok, E};
    (_) -> error
  end, maps:get(Ref, Results)).

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
      {{value, {LocalRef, Ty}}, Q} = queue:out(Queue),
      % sanity: don't convert something that is already in the global system
      [] = ets:lookup(?CACHE, LocalRef),
      {ErlangRecOrLocalRef, NewQ, {R1, R2}, NewCache} = do_convert({Ty, Res}, Q, LocalCache),
      convert(NewQ, {R1#{LocalRef => ErlangRecOrLocalRef}, group(R2, ErlangRecOrLocalRef, LocalRef)}, NewCache)
  end.

% create an unique type reference
-spec new_local_ref() -> temporary_ref().
new_local_ref() -> {local_ref, erlang:unique_integer()}.

-spec new_local_ref(ast_ty()) -> temporary_ref().
new_local_ref(Term) -> 
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
      Ref;
    _ -> 
      ets:insert(?TERMREFS, {Term, UniqueRef = new_local_ref()}),
      UniqueRef
  end,
  % additionally, if that generated reference was unified at the last step,
  % we replace that generated reference with the unified reference,
  % to be able to hit the global cache 
  % (no unified discarded reference appears in the global cache)
  case ets:lookup(?UNIFY, Reff) of
    [{Reff, UnifiedRef}] -> UnifiedRef;
    _ -> Reff 
  end.

-spec extend_symtab(ety_ref(), ety_ty_scheme()) -> _. 
extend_symtab({_, Namespace, Type, ArgsCount}, TyScheme) ->
  Ref = {Namespace, Type, ArgsCount},
  % io:format(user,"Extending symtab by ~p~n With scheme: ~p~n", [Ref, TyScheme]),
  ets:insert(?SYMTAB, {Ref, TyScheme}).

-spec lookup_ty(ety_ref()) -> ety_ty_scheme().
lookup_ty({ty_qref, A, B, C}) ->
  [{_, Scheme}] = ets:lookup(?SYMTAB, {A, B, C}),
  Scheme;
lookup_ty({ty_ref, A, B, C}) ->
  Ref = {A, B, C},
  % io:format(user,"Lookup: ~p~nin~n~p~n", [Ref, ets:tab2list(?SYMTAB)]),
  [{_, Scheme}] = ets:lookup(?SYMTAB, Ref),
  Scheme;
lookup_ty({R, A, B, C}) ->
  error(R),
  Ref = {A, B, C},
  [{_, Scheme}] = ets:lookup(?SYMTAB, Ref),
  Scheme.

-spec group(#{A => list(X)}, A, X) -> #{A := list(X)}.
group(M, Key, Value) ->
  maps:update_with(Key, fun(Group) -> [Value | Group] end, [Value], M).

% entrypoint for recursion: named type
-spec do_convert({ast_ty(), database()}, queue(), local_cache()) -> {ty_rec(), queue(), database(), local_cache()}.
do_convert({X = {named, _, Ref, Args}, R = {IdTy, _}}, Q, Cache) ->
  % add to create a reverse mapping between the internal result node and the named type
  case ets:lookup(?UNPARSE_NAMED_FINISHED, X) of
    [] -> ets:insert(?UNPARSE_NAMED_QUEUE, {X, []});
    _ -> ok % already processed
  end,

  case Cache of
    #{{Ref, Args} := NewRef} ->
      #{NewRef := Ty} = IdTy,
      {Ty, Q, R, Cache};
    _ ->
      % find ty in global table
      % io:format(user,"Lookup ~p~n", [Ref]),
      ({ty_scheme, Vars, Ty}) = lookup_ty(Ref),

      % FIXME ust subst:apply
      % Map = subst:from_list(lists:zip([V || {V, _Bound} <- Vars], Args)),
      % NewTy = subst:apply(Map, Ty, no_clean),
      Map = from_list(lists:zip([V || {V, _Bound} <- Vars], Args)),
      % we can do this since recursive variables should not descend "into" a named type
      NewTy = convert_back(debruijn(ty_parser:apply(Map, Ty, no_clean))),
      
      % sanity
      false = maps:is_key({Ref, Args}, Cache),

      NewRef = new_local_ref(X),
      case ets:lookup(?CACHE, NewRef) of 
        [] -> 
          % create a new reference (ref args pair), memoize, and add continue converting
          {InternalTy, NewQ, {R0, R1}, C0} = do_convert({NewTy, R}, Q, Cache#{{Ref, Args} => NewRef}),
          {InternalTy, NewQ, {R0#{NewRef => InternalTy}, group(R1, InternalTy, NewRef)}, C0};
        [{NewRef, CachedNode}] -> 
          % reuse type representation of the global cache
          InternalTy = ?NODE:load(CachedNode),
          {InternalTy, Q, R, Cache}
      end
  end;

% entrypoint for recursion: local equation
do_convert({AstTy = {mu, RecVar = {mu_var, Name}, Ty}, R}, Q, Cache) ->
  true = is_atom(Name),

  NewRef = new_local_ref(AstTy),
  % all binders should be unique, 
  % only binders with the same body are allowed to share the name
  case maps:is_key(RecVar, Cache) of
    false -> ok;
    true -> NewRef = maps:get(RecVar, Cache)
  end,
  NewCache = Cache#{RecVar => NewRef},
  {InternalTy, NewQ, {R0, R1}, C0} = do_convert({Ty, R}, Q, NewCache),
  % return record
  {InternalTy, NewQ, {R0#{NewRef => InternalTy}, group(R1, InternalTy, NewRef)}, C0};

% exit for recursion: local equation variable
do_convert({AstTy = {mu_var, Name}, R = {IdTy, _}}, Q, Cache) ->
  true = is_atom(Name),


  #{AstTy := Ref} = Cache,
  % We are allowed to load the memoized ref
  % because the second occurrence of the mu variable
  % is below a type constructor, 
  % i.e. the memoized reference is fully defined
  #{Ref := Ty} = IdTy,
  {Ty, Q, R, Cache};
 
% built-ins
do_convert({{predef, any}, R}, Q, Cache) -> {?TY:any(), Q, R, Cache};
do_convert({{predef, none}, R}, Q, Cache) -> {?TY:empty(), Q, R, Cache};
do_convert({{predef, atom}, R}, Q, Cache) -> {?TY:atom(dnf_ty_atom:any()), Q, R, Cache};
do_convert({{predef, integer}, R}, Q, Cache) -> {?TY:interval(dnf_ty_interval:any()), Q, R, Cache};
do_convert({{predef_alias, Alias}, R}, Q, Cache) -> do_convert({expand_predef_alias(Alias), R}, Q, Cache);

% predefined
do_convert({{fun_simple}, R}, Q, Cache) -> {?TY:functions(ty_functions:any()), Q, R, Cache};
do_convert({{tuple_any}, R}, Q, Cache) -> {?TY:tuples(ty_tuples:any()), Q, R, Cache};
do_convert({{empty_list}, R}, Q, Cache) -> {?TY:predefined(dnf_ty_predefined:predefined('[]')), Q, R, Cache};
do_convert({{predef, T}, R}, Q, Cache) when T == pid; T == port; T == reference; T == float ->
  {?TY:predefined(dnf_ty_predefined:predefined(T)), Q, R, Cache};
do_convert({{map_any}, R}, Q, Cache) ->
  {?TY:map(dnf_ty_map:any()), Q, R, Cache};

% bitstrings
do_convert({{bitstring}, R}, Q, Cache) ->
  {?TY:bitstring(dnf_ty_bitstring:any()), Q, R, Cache};

% atoms
do_convert({{singleton, Atom}, R}, Q, Cache) when is_atom(Atom) ->
  TAtom = dnf_ty_atom:finite([Atom]),
  {?TY:atom(TAtom), Q, R, Cache};

% intervals
do_convert({{singleton, I}, R}, Q, Cache) when is_integer(I) ->
  Int = dnf_ty_interval:interval(I, I),
  {?TY:interval(Int), Q, R, Cache};
do_convert({{range, From, To}, R}, Q, Cache) ->
  Int = dnf_ty_interval:interval(From, To),
  {?TY:interval(Int), Q, R, Cache};

% boolean operators
do_convert({{union, []}, R}, Q, Cache) -> {?TY:empty(), Q, R, Cache};
do_convert({{union, [A]}, R}, Q, Cache) -> do_convert({A, R}, Q, Cache);
do_convert({{union, [A|T]}, R}, Q, Cache) -> 
  {R1, Q1, RR1, C1} = do_convert({A, R}, Q, Cache),
  {R2, Q2, RR2, C2} = do_convert({{union, T}, RR1}, Q1, C1),
  {?TY:union(R1, R2), Q2, RR2, C2};

do_convert({{intersection, []}, R}, Q, Cache) -> {?TY:any(), Q, R, Cache};
do_convert({{intersection, [A]}, R}, Q, Cache) -> do_convert({A, R}, Q, Cache);
do_convert({{intersection, [A|T]}, R}, Q, Cache) -> 
  {R1, Q1, RR0, C0} = do_convert({A, R}, Q, Cache),
  {R2, Q2, RR1, C1} = do_convert({{intersection, T}, RR0}, Q1, C0),
  {?TY:intersect(R1, R2), Q2, RR1, C1};

do_convert({{negation, Ty}, R}, Q, Cache) -> 
  {NewR, Q0, RR0, C0} = do_convert({Ty, R}, Q, Cache),
  {?TY:negate(NewR), Q0, RR0, C0};

% variables
do_convert({{var, A}, R}, Q, Cache) ->
  % if this is a special $mu_integer()_name() variable, convert to that representation
  case string:prefix(atom_to_list(A), "#ety_") of 
    nomatch -> 
      {?TY:singleton(ty_variable:new_with_name(A)), Q, R, Cache};
    _IdName -> 
      error(todo_ety_variable_not_implemented) % TODO
      % assumption: erlang types generates variables only in this pattern: $mu_integer()_name()
      % [Id, Name] = string:split(IdName, "_"),
      % {ty_rec:s_variable(ty_variable:new_with_name_and_id(list_to_integer(Id), list_to_atom(Name))), Q, R}
  end;

% === term rewrites
do_convert({{nonempty_list, Ty}, R}, Q, Cache) ->
  do_convert({{nonempty_improper_list, Ty, {empty_list}}, R}, Q, Cache);
do_convert({{nonempty_improper_list, Ty, Term}, R}, Q, Cache) ->
  do_convert({{intersection, [{list, Ty}, {negation, Term}]} , R}, Q, Cache);
do_convert({{list, Ty}, R}, Q, Cache) ->
  do_convert({
  {union, [
    {improper_list, Ty, {empty_list}}, 
    {empty_list}
  ]}, R}, Q, Cache);

% rewrite maps into {Tuple, Function} tuples
do_convert({{map, AssocList}, R}, Q, Cache) ->
  {_, TupPart, FunPart} = lists:foldl(
    fun({Association, Key, Val}, {PrecedenceDomain, Tuples, Functions}) ->
      case Association of
        map_field_opt ->
          % tuples only
          Tup = {tuple, [{intersection, [Key, {negation, PrecedenceDomain}]}, Val]},
          {{union, [PrecedenceDomain, Key]}, {union, [Tuples, Tup]}, Functions};
        map_field_req ->
          % tuples & functions
          Tup = {tuple, [{intersection, [Key, {negation, PrecedenceDomain}]}, Val]},
          Fun = {fun_full, [{intersection, [Key, {negation, PrecedenceDomain}]}], Val},
          {{union, [PrecedenceDomain, Key]}, {union, [Tuples, Tup]}, {intersection, [Functions, Fun]}}
      end
    end, {{predef, none}, {predef, none}, {fun_simple}}, AssocList),
  MapTuple = {tuple, [TupPart, FunPart]},
  {Recc, Q0, R0, C0} = do_convert({MapTuple, R}, Q, Cache),
  {?TY:tuple_to_map(Recc), Q0, R0, C0};

% === nested data structures 
% === these can potentially create temporary references and can extend the queue
 
% functions
do_convert({{fun_full, Domains, CoDomain}, R}, Q, Cache) ->
  {ParsedDomains, Q0} = lists:foldl(
    fun(Element, {Components, OldQ}) ->
      {IdOrNode, QQ} = queue_if_new(Element, OldQ),
      {Components ++ [IdOrNode], QQ}
   end, {[], Q}, Domains),

  {ParsedCoDomain, Q1} = queue_if_new(CoDomain, Q0),
    
  T = ty_functions:singleton(length(Domains), dnf_ty_function:singleton(ty_function:function(ParsedDomains, ParsedCoDomain))),
  {?TY:functions(T), Q1, R, Cache};

% tuples
do_convert({{tuple, Comps}, R}, Q, Cache) ->
  {ParsedComponents, Q0} = lists:foldl(
    fun(Element, {Components, OldQ}) ->
      {IdOrNode, QQ} = queue_if_new(Element, OldQ),
      {Components ++ [IdOrNode], QQ}
    end, {[], Q}, Comps),
    
  T = ty_tuples:singleton(length(Comps), dnf_ty_tuple:singleton(ty_tuple:tuple(ParsedComponents))),
  {?TY:tuples(T), Q0, R, Cache};

% lists
do_convert({{improper_list, A, B}, R}, Q, Cache) ->
  {T1, Q0} = queue_if_new(A, Q),
  {T2, Q1} = queue_if_new(B, Q0),
    
  {?TY:list(dnf_ty_list:singleton(ty_list:tuple([T1, T2]))), Q1, R, Cache};

% maps 

do_convert(T, _Q, _) ->
  io:format(user,"~p~n", [T]),
  erlang:error({"Transformation from ast:ty() to ty_rec:ty() not implemented or malformed type", T}).

-spec queue_if_new(ast_ty(), queue()) -> {type() | temporary_ref(), queue()}.
queue_if_new(Element, Queue) ->
  Id = new_local_ref(Element),
  case ets:lookup(?CACHE, Id) of
    % to be converted later, add to queue, return temporary reference
    [] -> {Id, queue:in({Id, Element}, Queue)};
    % if already known, don't process and return a real reference
    [{Id, Node}] -> {Node, Queue}
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
        lists:foreach(fun(E) -> true = ets:insert_new(?UNIFY, {E, H}) end, T),
        {H, T} 
      end
    || K := (V = [H | T]) <- TyToIds, length(V) > 1}), 

  % replace equivalent refs with representative
  ToReplace = maps:from_list(lists:flatten([[{Single, Represent} || Single <- Dupl ] || {_, {Represent, Dupl}}<- ToUnify])),
  utils:replace({Ref, IdToTy}, ToReplace).

unparse(Node) ->
  case ets:lookup(?UNPARSE_CACHE, Node) of
    [{_, Ref}] -> 
      persistent_term:get(Ref);
    _ ->
      {R, _} = ty_node:unparse(Node, #{}),

      Ref = make_ref(),
      persistent_term:put(Ref, R),
      % inserting R into ets (as a value) is extremely slow if R is a big term
      true = ets:insert_new(?UNPARSE_CACHE, {Node, Ref}),
      
      R
  end.

% FIXME remove once integrated
% -spec expand_predef_alias(ast:predef_alias_name()) -> ast:ty(). %TODO
expand_predef_alias(term) -> {predef, any};
% TODO better binaries
expand_predef_alias(binary) -> {bitstring};
expand_predef_alias(nonempty_binary) -> {bitstring};
expand_predef_alias(bitstring) -> {bitstring};
expand_predef_alias(nonempty_bitstring) -> {bitstring};
expand_predef_alias(boolean) -> {union, [{singleton, true}, {singleton, false}]};
expand_predef_alias(byte) -> {range, 0, 255};
expand_predef_alias(char) -> {range, 0, 1114111};
expand_predef_alias(nil) -> {empty_list};
expand_predef_alias(number) -> {union, [{predef, float}, {predef, integer}]};
expand_predef_alias(list) -> {list, {predef, any}};
% also see code in ast_transform for expanding predefined aliases applied to arguments
expand_predef_alias(nonempty_list) -> {nonempty_list, {predef, any}};
expand_predef_alias(maybe_improper_list) -> {improper_list, {predef, any}, {predef, any}};
expand_predef_alias(nonempty_maybe_improper_list) -> {nonempty_list, {predef, any}};
expand_predef_alias(string) -> {list, expand_predef_alias(char)};
expand_predef_alias(nonempty_string) -> {nonempty_list, expand_predef_alias(char)};
expand_predef_alias(iodata) -> {union, [expand_predef_alias(iolist), expand_predef_alias(binary)]};
expand_predef_alias(iolist) ->
    % TODO fix variable IDs
    RecVarID = erlang:unique_integer(),
    Var = {var, erlang:list_to_atom("mu" ++ integer_to_list(RecVarID))},
    RecType = {improper_list, {union, [expand_predef_alias(byte), expand_predef_alias(binary), Var]}, {union, [expand_predef_alias(binary), {empty_list}]}},
    {mu, Var, RecType};
expand_predef_alias(map) -> {map, [{map_field_opt, {predef, any}, {predef, any}}]};
expand_predef_alias(function) -> {fun_simple};
expand_predef_alias(module) -> {predef, atom};
expand_predef_alias(mfa) -> {tuple, [{predef, atom}, {predef, atom}, {predef, integer}]};
expand_predef_alias(arity) -> {predef, integer};
expand_predef_alias(identifier) -> {union, [{predef, pid}, {predef, port}, {predef, reference}]};
expand_predef_alias(node) -> {predef, atom};
expand_predef_alias(timeout) -> {union, [{singleton, infinity}, expand_predef_alias(non_neg_integer)]};
expand_predef_alias(no_return) -> {predef, none};
expand_predef_alias(non_neg_integer) -> {range, 0, '*'};
expand_predef_alias(pos_integer) -> {range, 1, '*'};
expand_predef_alias(neg_integer) -> {range, '*', -1};

expand_predef_alias(Name) ->
    logger:error("Not expanding: ~p", [Name]),
    errors:not_implemented(utils:sformat("expand_predef_alias for ~w", Name)).



% FIXME remove once integrated into Etylizer
apply(S, T, _) -> apply_base(S, T).

apply_base(S, T) ->
    case T of
        {singleton, _} -> T;
        {bitstring} -> T;
        {empty_list} -> T;
        {list, U} -> {list, apply_base(S, U)};
        {mu, V, U} -> {mu, V, apply_base(S, U)};
        {nonempty_list, U} -> {nonempty_list, apply_base(S, U)};
        {improper_list, U, V} -> {improper_list, apply_base(S, U), apply_base(S, V)};
        {nonempty_improper_list, U, V} -> {nonempty_improper_list, apply_base(S, U), apply_base(S, V)};
        {fun_simple} -> T;
        {fun_any_arg, U} -> {fun_any_arg, apply_base(S, U)};
        {fun_full, Args, U} -> {fun_full, apply_list(S, Args), apply_base(S, U)};
        {range, _, _} -> T;
        {map_any} -> T;
        {map, Assocs} ->
            {map, lists:map(fun({Kind, U, V}) -> {Kind, apply_base(S, U), apply_base(S, V)} end, Assocs)};
        {predef, _} -> T;
        {predef_alias, _} -> T;
        {record, Name, Fields} ->
            {record, Name,
             lists:map(fun({FieldName, U}) -> {FieldName, apply_base(S, U)} end, Fields)};
        {named, Loc, Ref, Args} ->
            {named, Loc, Ref, apply_list(S, Args)};
        {tuple_any} -> T;
        {tuple, Args} -> {tuple, apply_list(S, Args)};
        {var, Alpha} ->
            case maps:find(Alpha, S) of
                error -> {var, Alpha};
                {ok, U} -> U
            end;
        {mu_var, Alpha} -> {mu_var, Alpha};
        {union, Args} -> {union, apply_list(S, Args)};
        {intersection, Args} -> {intersection, apply_list(S, Args)};
        {negation, U} -> {negation, apply_base(S, U)}
    end.

apply_list(S, L) -> lists:map(fun(T) -> apply_base(S, T) end, L).

from_list(L) -> maps:from_list(L).



%% Main conversion function
debruijn(Type) ->
    debruijn(Type, []).

%% Conversion helper with environment stack
debruijn({singleton, _} = T, _Env) -> T;
debruijn({bitstring}, _Env) -> {bitstring};
debruijn({empty_list}, _Env) -> {empty_list};
debruijn({list, U}, Env) -> {list, debruijn(U, Env)};
debruijn({mu, {mu_var, Name}, Body}, Env) ->
    NewEnv = [Name | Env],
    {mu, debruijn(Body, NewEnv)};
debruijn({nonempty_list, U}, Env) -> {nonempty_list, debruijn(U, Env)};
debruijn({improper_list, U, V}, Env) -> 
    {improper_list, debruijn(U, Env), debruijn(V, Env)};
debruijn({nonempty_improper_list, U, V}, Env) -> 
    {nonempty_improper_list, debruijn(U, Env), debruijn(V, Env)};
debruijn({fun_simple}, _Env) -> {fun_simple};
debruijn({fun_any_arg, U}, Env) -> {fun_any_arg, debruijn(U, Env)};
debruijn({fun_full, Args, U}, Env) -> 
    {fun_full, debruijn_list(Args, Env), debruijn(U, Env)};
debruijn({range, Min, Max}, _Env) -> {range, Min, Max};
debruijn({map_any}, _Env) -> {map_any};
debruijn({map, Assocs}, Env) ->
    {map, lists:map(fun({Kind, U, V}) -> 
        {Kind, debruijn(U, Env), debruijn(V, Env)} 
    end, Assocs)};
debruijn({predef, Name}, _Env) -> {predef, Name};
debruijn({predef_alias, Name}, _Env) -> {predef_alias, Name};
debruijn({named, Loc, Ref, Args}, Env) ->
    {named, Loc, Ref, debruijn_list(Args, Env)};
debruijn({tuple_any}, _Env) -> {tuple_any};
debruijn({tuple, Args}, Env) -> {tuple, debruijn_list(Args, Env)};
debruijn({mu_var, Name}, Env) ->
    case index_of(Name, Env) of
        {ok, Index} -> {mu_var, Index};
        not_found -> error({unbound_variable, Name})
    end;
debruijn({var, Alpha}, Env) ->
    case index_of(Alpha, Env) of
        {ok, Index} -> {mu_var, Index};
        not_found -> {var, Alpha}
    end;
debruijn({union, Args}, Env) -> {union, debruijn_list(Args, Env)};
debruijn({intersection, Args}, Env) -> {intersection, debruijn_list(Args, Env)};
debruijn({negation, U}, Env) -> {negation, debruijn(U, Env)}.

%% Helper to debruijn lists of types
debruijn_list(Types, Env) ->
    [debruijn(T, Env) || T <- Types].

%% Helper to find the index of a name in the environment
index_of(Name, Env) ->
    index_of(Name, Env, 0).

index_of(Name, [Name|_], Index) -> {ok, Index};
index_of(Name, [_|Rest], Index) -> index_of(Name, Rest, Index + 1);
index_of(_, [], _) -> not_found.



%% Conversion back to named variables with fresh names
convert_back(Type) ->
    {Result, _} = convert_back(Type, [], 0),
    Result.

%% Helper for conversion back to named variables
convert_back({mu, Body}, Env, Counter) ->
    Name = make_fresh_name(Counter),
    NewEnv = [Name | Env],
    {ConvertedBody, NewCounter} = convert_back(Body, NewEnv, Counter + 1),
    {{mu, {mu_var, Name}, ConvertedBody}, NewCounter};
convert_back({mu_var, Index}, Env, Counter) ->
    case lists:nth(Index + 1, Env) of
        Name -> {{mu_var, Name}, Counter}
    end;
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
convert_back(Type, Env, Counter) when is_tuple(Type) ->
    case element(1, Type) of
        Constructor when Constructor =:= list; 
                         Constructor =:= nonempty_list ->
            [Constructor, Arg] = tuple_to_list(Type),
            {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
            {list_to_tuple([Constructor, ConvertedArg]), NewCounter};
        Constructor when Constructor =:= improper_list;
                         Constructor =:= nonempty_improper_list ->
            [Constructor, Arg, Arg2] = tuple_to_list(Type),
            {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
            {ConvertedArg2, NewCounter2} = convert_back(Arg2, Env, NewCounter),
            {list_to_tuple([Constructor, ConvertedArg, ConvertedArg2]), NewCounter2};
        Constructor when Constructor =:= fun_any_arg;
                         Constructor =:= negation ->
            [Constructor, Arg] = tuple_to_list(Type),
            {ConvertedArg, NewCounter} = convert_back(Arg, Env, Counter),
            {list_to_tuple([Constructor, ConvertedArg]), NewCounter};
        fun_full ->
            [fun_full, Args, Ret] = tuple_to_list(Type),
            {ConvertedArgs, Counter1} = convert_back_list(Args, Env, Counter),
            {ConvertedRet, NewCounter} = convert_back(Ret, Env, Counter1),
            {{fun_full, ConvertedArgs, ConvertedRet}, NewCounter};
        map ->
            [map, Assocs] = tuple_to_list(Type),
            {ConvertedAssocs, NewCounter} = convert_back_assocs(Assocs, Env, Counter),
            {{map, ConvertedAssocs}, NewCounter};
        named ->
            [named, Loc, Ref, Args] = tuple_to_list(Type),
            {ConvertedArgs, NewCounter} = convert_back_list(Args, Env, Counter),
            {{named, Loc, Ref, ConvertedArgs}, NewCounter};
        _ ->
            {Type, Counter} % For atomic types
    end;
convert_back(Type, _Env, Counter) ->
    {Type, Counter}. % For non-tuple types

%% Helper functions
convert_back_list([], _Env, Counter) -> {[], Counter};
convert_back_list([Type|Rest], Env, Counter) ->
    {Converted, Counter1} = convert_back(Type, Env, Counter),
    {ConvertedRest, NewCounter} = convert_back_list(Rest, Env, Counter1),
    {[Converted|ConvertedRest], NewCounter}.

convert_back_assocs([], _, Counter) -> {[], Counter};
convert_back_assocs([{Kind, K, V}|Rest], Env, Counter) ->
    {ConvertedK, Counter1} = convert_back(K, Env, Counter),
    {ConvertedV, Counter2} = convert_back(V, Env, Counter1),
    {ConvertedRest, NewCounter} = convert_back_assocs(Rest, Env, Counter2),
    {[{Kind, ConvertedK, ConvertedV}|ConvertedRest], NewCounter}.

make_fresh_name(Counter) ->
    list_to_atom("$var_" ++ integer_to_list(Counter)).

