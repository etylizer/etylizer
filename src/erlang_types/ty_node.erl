-module(ty_node).

-export([
  init/0, 
  clean/0
]).

-export([
  unparse/2,

  dump/1, 
  dumpp/1,

  compare/2,
  make/1,
  is_consed/1,
  is_defined/1,
  new_ty_node/0,
  define/2,
  load/1,

  is_empty/1, 
  normalize/2,
  leq/2,

  % used by types that contain ty_node references
  is_empty/2,
  normalize/3,
  leq/3,

  negate/1,
  intersect/2,
  union/2,
  difference/2,
  disjunction/1,
  conjunction/1,

  any/0,
  empty/0,

  all_variables/1,
  all_variables/2,
  substitute/2,

  force_load/2
]).


-export_type([
  type/0, 
  cache/0,
  all_variables_cache/0
]).

-opaque type() :: {node, term()}.
-opaque cache() :: #{type() => boolean()}.
-opaque all_variables_cache() :: #{type() => _}.
-type normalize_cache() :: #{{type_descriptor(), monomorphic_variables()} => boolean()}.
-type type_descriptor() :: dnf_ty_variable:type().
-type temporary_type() :: {local_ref, term()}. % used in ty_parser
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type monomorphic_variables() :: etally:monomorphic_variables().
-type ast_mu_var() :: ast:ty_mu_var().
-type ast_ty() :: ast:ty().
-type variable() :: ty_variable:type().

-behaviour(global_state).

-define(ID, ty_node_id).
-define(SYSTEM, ty_node_system).
-define(UNIQUETABLE, ty_record_to_node).
-define(P, ty_node_p).
-define(N, ty_node_n).
-define(CACHE, ty_node_cache).
-define(NORMCACHE, ty_node_normalize_cache).
-define(OPCACHE, ty_node_op_cache).
-define(ALL_ETS, [?ID, ?SYSTEM, ?P, ?N, ?UNIQUETABLE, ?CACHE, ?NORMCACHE, ?OPCACHE]).
-define(TY, dnf_ty_variable).

-spec init() -> _.
init() ->
  case ets:whereis(?ID) of
      undefined -> 
        [ets:new(T, [public, set, named_table]) || T <- ?ALL_ETS],
        ets:insert(?ID, {id, 0});
      _ -> 
        ok % cleanup()
  end,
  % io:format(user, "ty_node state initialized~n", []).
  ok.

-spec clean() -> _.
clean() ->
  case ets:whereis(?ID) of
      undefined -> ok;
      _ -> 
        [ets:delete(T) || T <- ?ALL_ETS]
  end.

-spec compare(T, T) -> eq | lt | gt when T :: type() | temporary_type().
compare({node, Id1}, {node, Id2}) when Id1 < Id2 -> lt;
compare({node, Id1}, {node, Id2}) when Id1 > Id2 -> gt;
compare({node, _Id1}, {node, _Id2}) -> eq;
% this is an architecture hack;
% ty_node is used differently in ty_parser with local references
% ty_node has to support comparing these local temporary references
compare({local_ref, Id1}, {local_ref, Id2}) when Id1 < Id2 -> lt;
compare({local_ref, Id1}, {local_ref, Id2}) when Id1 > Id2 -> gt;
compare({local_ref, _Id1}, {local_ref, _Id2}) -> eq;
% now this gets hacky
% we need to ensure that comparing these two structures behaves as if 
% the local_ref was replaced, i.e. the order result be the same
% before and after replacing the local_ref
% otherwise we get invalid BDDs
compare(L = {local_ref, _}, N = {node, _}) -> 
  compare(ty_parser:lookup_ref(L), N);
compare(N = {node, _}, L = {local_ref, _}) -> 
  compare(N, ty_parser:lookup_ref(L)).

-spec make(type_descriptor()) -> type().
make(Ty) ->
  Res = ets:lookup(?UNIQUETABLE, Ty),
  case Res of
    [{_, Ref}] -> Ref;
    _ -> define(new_ty_node(), Ty)
  end.

-spec is_consed(type_descriptor()) -> {true, type()} | false.
is_consed(Ty) ->
  Res = ets:lookup(?UNIQUETABLE, Ty),
  case Res of
    [{Ty, Node}] -> {true, Node};
    _ -> false
  end.

-spec is_defined(type()) -> boolean().
is_defined(Node) ->
  Res = ets:lookup(?SYSTEM, Node),
  case Res of
    [{_, _}] -> true;
    _ -> false
  end.

-spec new_ty_node() -> type().
new_ty_node() ->
  {node, next_id()}.

-spec define(T, type_descriptor()) -> T when T :: type().
define(Reference, Node) ->
  % io:format(user,"  +++++++++++++~nStore: ~p~n~p~n  +++++++++++++~n", [Reference, Node]),
  dnf_ty_variable:assert_valid(Node),
  [] = ets:lookup(?SYSTEM, Reference),
  [] = ets:lookup(?UNIQUETABLE, {Node, Reference}),
  ets:insert(?SYSTEM, {Reference, Node}),
  ets:insert(?UNIQUETABLE, {Node, Reference}),
  Reference.

% for loading serialized test types through dump/1
-spec force_load(T, type_descriptor()) -> T when T :: type().
force_load(Reference = {node, Id}, Node) ->
  ets:insert(?SYSTEM, {Reference, Node}),
  ets:insert(?UNIQUETABLE, {Node, Reference}),
  % update counter
  CurrentId = ets:update_counter(?ID, id, 0),
  case CurrentId < Id of
    true -> 
      ets:update_counter(?ID, id, (Id - CurrentId + 1));
    _ -> ok
  end,
  Reference.


-spec load(type()) -> type_descriptor().
load(TyNode) ->
  [{TyNode, Ty}] = ets:lookup(?SYSTEM, TyNode),
  Ty.
  
-spec leq(T, T) -> boolean() when T :: type().
leq(T1, T2) ->
  is_empty(difference(T1, T2)).

-spec leq(T, T, ST) -> {boolean(), ST} when T :: type().
leq(T1, T2, Cache) ->
  is_empty(difference(T1, T2), Cache).

-spec is_empty(type()) -> boolean().
is_empty(TyNode) ->
  case ets:lookup(?CACHE, TyNode) of
    [{_, R}] -> R;
    [] ->
      % T0 = os:system_time(microsecond),
      {Result, LocalCache} = is_empty(TyNode, #{}),
      % io:format(user,"Empty ~p in ~p us~n", [TyNode, os:system_time(microsecond)-T0]),
      utils:update_ets_from_map(?CACHE, LocalCache),
      ets:insert(?CACHE, [{TyNode, Result}]),
      Result
  end.

% see Frisch PhD thesis
% this implements the caching variant of the recursive system chapter
% locally, without using a global hash table and a global stack
% TODO 
%   implement backtracking-free algorithm after finding a test case
%   where caching *during* the recursive computation would benefit
%   the time to solve
-spec is_empty(type(), cache()) -> {boolean(), cache()}.
is_empty(TyNode, LocalCache) ->
  Ty = load(TyNode),

  case LocalCache of
    #{Ty := Res} -> {Res, LocalCache};
    _ -> 
      % assume type is empty and add to state
      % N U {t}
      {Result, LC_0} = ?TY:is_empty(Ty, LocalCache#{Ty => true}),

      case Result of 
        % empty; 
        % local cache can be kept as is 
        % Ty is empty is now cached, and all intermediate results are also cached
        true -> {true, LC_0};

        % not empty;
        % invalidate all types that were assumed to be empty
        %  => recover initial N
        % and add Ty to be non-empty to the cache
        % we don't need to backtrack (there is no single global cache), 
        % use the LocalCache from the arguments
        false -> {false, LocalCache#{Ty => false}}
      end
  end.

-spec negate(T) -> T when T :: type().
negate(T) ->
  opcache({n, T}, fun() -> make(?TY:negate(load(T))) end).

-spec intersect(T, T) -> T when T :: type().
intersect(T1, T2) ->
  opcache({i, T1, T2}, fun() -> make(?TY:intersect(load(T1), load(T2))) end).

-spec union(T, T) -> T when T :: type().
union(T1, T2) ->
  opcache({u, T1, T2}, fun() -> make(?TY:union(load(T1), load(T2))) end).

-spec difference(T, T) -> T when T :: type().
difference(T1, T2) ->
  opcache({d, T1, T2}, fun() -> make(?TY:difference(load(T1), load(T2))) end).

-spec any() -> type().
any() ->
  make(?TY:any()).

-spec empty() -> type().
empty() ->
  make(?TY:empty()).

-spec disjunction([type()]) -> type().
disjunction(Nodes) ->
  lists:foldl(fun(E, Acc) -> union(E, Acc) end, empty(), Nodes).

-spec conjunction([type()]) -> type().
conjunction(Nodes) ->
  lists:foldl(fun(E, Acc) -> intersect(E, Acc) end, any(), Nodes).

-spec dumpp(type()) -> {type(), #{type() => type_descriptor()}}.
dumpp(Ty) ->
  {Ty, dump(Ty)}.

-spec dump(type()) -> #{type() => type_descriptor()}.
dump(Ty) ->
  do_dump([Ty], #{}).

-spec do_dump([type()], M) -> M when M :: #{type() => type_descriptor()}.
do_dump([], Res) -> Res;
do_dump([Ty | T], Res) ->
  case maps:is_key(Ty, Res) of
    true -> do_dump(T, Res);
    false -> 
      Rec = load(Ty),
      MoreTys = utils:everything(
        fun(E = {node, _}) -> {ok, E};(_) -> error end,
        Rec
      ),
      do_dump(T ++ MoreTys, Res#{Ty => Rec})
  end.


% =============
% Tallying
% =============

% tally phase 1, see POPL part 2
% TODO backtrack-free algorithm, see subtyping comment
-spec normalize(type(), monomorphic_variables()) -> set_of_constraint_sets().
normalize(TyNode, FixedVariables) ->
  Z = case ets:lookup(?NORMCACHE, {TyNode, FixedVariables}) of
    [{_, Result}] -> Result;
    [] ->
      % T0 = os:system_time(millisecond),
      {Result, _LocalCache} = normalize(TyNode, FixedVariables, #{}),
      ets:insert(?NORMCACHE, [{{TyNode, FixedVariables}, Result}]),
      % case (os:system_time(millisecond)-T0) > 10000 of
      %   true -> 
      %     io:format(user, "~p~n", [ty_node:dump(TyNode)]),
      %     error(eend);
      %   _ -> ok
      % end,
      % io:format(user,"Normalize ~p in ~p ms~n", [TyNode, os:system_time(millisecond)-T0]),
      Result
  end,
  Z.

-spec normalize(type(), monomorphic_variables(), ST) -> {set_of_constraint_sets(), ST} when ST :: normalize_cache().
normalize(TyNode, FixedVariables, Cache) ->
  Ty = load(TyNode),

  case Cache of
    #{{Ty, FixedVariables} := Res} -> 
      {Res, Cache};
    _ -> 
      % assume type is normalized and add to local cache
      {Result, LC_0} = dnf_ty_variable:normalize(Ty, FixedVariables, Cache#{{Ty, FixedVariables} => [[]]}),

      case Result of 
        % satisfiable; 
        % local cache can be kept as is 
        % Ty is empty is now cached, and all intermediate results are also cached
        [[]] -> 
          {[[]], LC_0};

        % not (immediately) satisfiable;
        % invalidate all types that were assumed to be satisfiable
        %  => recover initial cache
        % and add the result of Ty to the cache
        % this is a bigger approximation than in the subtyping algorithm,
        % as the result could still be satisfiable
        % only [] is surely unsatisfiable
        Normalized -> 
          {Normalized, Cache#{{Ty, FixedVariables} => Normalized}}
      end
  end.

-spec unparse(type(), ST) -> {ast_ty(), ST} when ST :: #{type() => ast_mu_var()}.
unparse(Node = {node, Id}, Cache) -> 
  case ty_parser:unparse_mapping(Node) of
    {hit, Result} -> 
      {Result, Cache};
    _ ->
      case Cache of
        #{Node := RecVar} -> 
          {RecVar, Cache};
        _ -> 
          % a node can map to the recursive variable with the same identifier
          RecVar = {mu_var, erlang:list_to_atom("$node_" ++ integer_to_list(Id))},

          % sanity
          false = maps:is_key(Node, Cache),
          NewCache = Cache#{Node => RecVar},

          % load and continue
          Ty = ty_node:load(Node),
          {R, C0} = dnf_ty_variable:unparse(Ty, NewCache),

          % make type equation (if needed)
          Vars = ast_utils:referenced_recursive_variables(R),
          FinalTy = case lists:member(RecVar, Vars) of 
            true -> {mu, RecVar, R};
            false -> R
          end,

          % FIXME parallel cache not needed anymore
          % parallel cache
          % overwrite the recursion variable reference so that the whole binder + body is returned
          % otherwise there are recursion variables left-over which are unbounded
          {FinalTy, C0#{Node => FinalTy}}
      end
  end.

% ===
% substitution
% ===
% FIXME hack: unparse, substitute, then parse again
-spec substitute(type(), #{variable() => type()}) -> type().
substitute(Node, Varmap) ->
  T1 = ty_parser:unparse(Node),
  Subst = #{begin {{var, Name}, _} = ty_variable:unparse(K, #{}), Name end => ty_parser:unparse(V) || K := V <- Varmap},
  Res = subst:apply(Subst, T1, no_clean),
  ty_parser:parse(Res).

-spec all_variables(type()) -> sets:set(variable()).
all_variables(Ty) ->
  all_variables(Ty, #{}).

-spec all_variables(type(), all_variables_cache()) -> sets:set(variable()).
all_variables(Ty, Cache) ->
  case Cache of
    #{Ty := _}-> sets:new();
    _ ->
      dnf_ty_variable:all_variables(load(Ty), Cache#{Ty => []})
  end.

% helper functions
-spec opcache(term(), fun(() -> A)) -> A.
opcache(Key, F) ->
  % process dict faster but we can't erase just parts of it, only everything
  case ets:lookup(?OPCACHE, Key) of
    [{_, Result}] -> Result;
    [] ->
      R = F(),
      ets:insert(?OPCACHE, [{Key, R}]),
      R
  end.

-spec next_id() -> pos_integer().
next_id() ->
  NextId = ets:update_counter(?ID, id, 1),
  NextId.
