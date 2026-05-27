-module(ty_node).

-export([
  init/0, 
  clean/0
]).

-export([
  unparse/2,

  dump/1, 
  dumpp/1,
  dump_list/1,

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
  type/0
]).

-behaviour(global_state).

-include("erlang_types.hrl").
-include("etylizer.hrl").

-type type() :: {node, integer()}.
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().


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

-spec compare(T, T) -> eq | lt | gt when T :: type().
compare({node, Id1}, {node, Id2}) when Id1 < Id2 -> lt;
compare({node, Id1}, {node, Id2}) when Id1 > Id2 -> gt;
compare({node, _Id1}, {node, _Id2}) -> eq.

-spec make(type_descriptor()) -> type().
make(Ty) ->
  Res = ets:lookup(?UNIQUETABLE, Ty),
  case Res of
    [{_, Ref}] -> ?assert_type(Ref, type());
    [_ | _] -> error(invariant); % single result
    _ -> define(new_ty_node(), Ty)
  end.

-spec is_consed(type_descriptor()) -> {true, type()} | false.
is_consed(Ty) ->
  Res = ets:lookup(?UNIQUETABLE, Ty),
  case Res of
    [{Ty, Node}] -> {true, ?assert_type(Node, type())};
    [_ | _] -> error(invariant); % single result
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
  ?assert_pattern([], ets:lookup(?SYSTEM, Reference)),
  ?assert_pattern([], ets:lookup(?UNIQUETABLE, {Node, Reference})), ets:insert(?SYSTEM, {Reference, Node}),
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
  case ets:lookup(?SYSTEM, TyNode) of
    [{_, Ty}] -> ?assert_type(Ty, type_descriptor());
    _ -> error(invariant)
  end.
  
-spec leq(T, T) -> boolean() when T :: type().
leq(T1, T2) ->
  is_empty(difference(T1, T2)).

-spec leq(T, T, ST) -> {boolean(), ST} when T :: type(), ST :: is_empty_cache().
leq(T1, T2, Cache) ->
  is_empty(difference(T1, T2), Cache).

-spec is_empty(type()) -> boolean().
is_empty(TyNode) ->
  case ets:lookup(?CACHE, TyNode) of
    [{_, R}] -> ?assert_type(R, boolean());
    [_ | _] -> error(invariant);
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
-spec is_empty(type(), S) -> {boolean(), S} when S :: is_empty_cache().
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
        fun(E = {node, Id}) when is_integer(Id) -> {ok, E}; (_) -> error end,
        Rec
      ),
      do_dump(T ++ MoreTys, Res#{Ty => Rec})
  end.

-spec dump_list([{type(), type()}]) -> [#{type() => type_descriptor()}].
dump_list(List) ->
  lists:map(fun dump/1, 
    sets:to_list(
      lists:foldl(
        fun({A, B}, Acc) -> 
          sets:add_element(A, sets:add_element(B, Acc))
        end,
        sets:new(),
        List
      )
    )
  ).


% =============
% Tallying
% =============

% tally phase 1, see POPL part 2
% TODO backtrack-free algorithm, see subtyping comment
-spec normalize(type(), monomorphic_variables()) -> set_of_constraint_sets().
normalize(TyNode, FixedVariables) ->
  Z = case ets:lookup(?NORMCACHE, {TyNode, FixedVariables}) of
    [{_, Result}] -> ?assert_type(Result, set_of_constraint_sets());
    [_ | _] -> error(invariant);
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

-spec normalize(type(), monomorphic_variables(), ST) -> 
    {set_of_constraint_sets(), ST} when ST :: normalize_cache().
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

-spec unparse(type(), ST) -> {ast_ty(), ST} when ST :: unparse_cache().
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
          ?assert_pattern(false, maps:is_key(Node, Cache)),
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
% Native substitution on the internal BDD representation.
% Unlike the old unparse/parse hack, this preserves frame variable identities,
% which avoids the proliferation of fresh frame variables across substitution
% rounds (e.g. inside etally:unify).
% ===
-spec substitute(type(), #{variable() => type()}) -> type().
substitute(Node, Varmap) ->
  % Filter out frame variables TODO crash instead, caller should not use frame vars
  Sigma = maps:fold(
    fun(K, V, Acc) ->
            case ty_variable:is_frame(K) of
                {true, _} -> Acc;
                {false, _} -> Acc#{K => V}
            end
    end, #{}, Varmap),
  case maps:size(Sigma) of
    0 -> Node;
    _ -> do_substitute(Node, Sigma)
  end.

-spec do_substitute(type(), #{variable() => type()}) -> type().
do_substitute(Node, Sigma) ->
  Dom = sets:from_list(maps:keys(Sigma)),
  % Walk reachable nodes; only those whose variable set intersects dom(Sigma) need substitution.
  NeedsSub = collect_needs_sub(Node, Dom),
  case maps:is_key(Node, NeedsSub) of
    false -> Node;
    true ->
      % Pre-allocate fresh ty_node IDs as placeholders. The two-phase scheme
      % lets us handle recursive references: cycles in the substitution image
      % loop back to the new placeholders.
      Placeholders = maps:map(fun(_K, _V) -> new_ty_node() end, NeedsSub),
      % Compute the substituted body for each placeholder. 
      % Reorder to restore the BDD invariant
      Bodies0 = maps:fold(
        fun(OldNode, Placeholder, Acc) ->
          OldBdd = load(OldNode),
          NewBdd = dnf_ty_variable:substitute(OldBdd, Sigma, Placeholders),
          Acc#{Placeholder => dnf_ty_variable:reorder(NewBdd)}
        end, #{}, Placeholders),
      StartRef = maps:get(Node, Placeholders),
      % Topological define-with-consing. Without this, every call would leak
      % fresh ty_node IDs that already exist globally, defeating consing.
      unify_and_define(StartRef, Bodies0)
  end.

% Returns the consed/defined ty_node for StartRef after reusing globally
% consed nodes (and run-local equivalents) wherever possible.
-spec unify_and_define(type(), #{type() => type_descriptor()}) -> type().
unify_and_define(StartRef, Bodies) ->
  {DefineOrder, RevGraph} = topo_sccs(Bodies),
  {FinalStartRef, FinalBodies} = consing_pass(DefineOrder, RevGraph, StartRef, Bodies),
  define_remaining(FinalBodies),
  FinalStartRef.

% Build the dependency graph (only edges within Bodies; external refs need no
% ordering), compute SCCs, and return them in reverse-topological order along
% with the reverse graph (for back-reference rewriting).
-spec topo_sccs(#{type() => type_descriptor()}) -> {[[type()]], #{type() => [type()]}}.
topo_sccs(Bodies) ->
  KeySet = sets:from_list(maps:keys(Bodies)),
  Graph = build_internal_graph(Bodies, KeySet),
  RevGraph = tarjan:reverse_graph(Graph),
  % tarjan widens Node to term(); we know inputs are type(), so re-tag.
  {SCCsRaw, CondensedRaw} = tarjan:condense(Graph),
  SCCs = ?assert_type(SCCsRaw, #{type() => type()}),
  Condensed = ?assert_type(CondensedRaw, #{type() => [type()]}),
  Components = group_components(SCCs),
  Sort = ?assert_type(tarjan:dfs(Condensed), [type()]),
  DefineOrder = [maps:get(R, Components) || R <- Sort],
  {DefineOrder, RevGraph}.

-spec build_internal_graph(#{type() => type_descriptor()}, sets:set(type())) ->
    #{type() => [type()]}.
build_internal_graph(Bodies, KeySet) ->
  maps:fold(
    fun(R, B, Acc) ->
      Internal = [C || C <- collect_node_refs(B), sets:is_element(C, KeySet)],
      Acc#{R => lists:usort(Internal)}
    end, #{}, Bodies).

-spec group_components(#{type() => type()}) -> #{type() => [type()]}.
group_components(SCCs) ->
  Acc0 = ?assert_type(#{}, #{type() => [type()]}),
  lists:foldl(
    fun({N, Root}, Acc) ->
      maps:update_with(Root, fun(Ns) -> [N | Ns] end, [N], Acc)
    end, Acc0, lists:sort(maps:to_list(SCCs))).

% Walk SCCs in topological order, redirecting nodes whose body is already
% globally consed (or appeared earlier in this run).
-spec consing_pass([[type()]], #{type() => [type()]}, type(),
                   #{type() => type_descriptor()}) ->
    {type(), #{type() => type_descriptor()}}.
consing_pass(DefineOrder, RevGraph, StartRef, Bodies) ->
  LocalDefs0 = ?assert_type(#{}, #{type_descriptor() => type()}),
  {S, B, _} = lists:foldl(
    fun(SCC, Acc) -> process_scc(SCC, RevGraph, Acc) end,
    {StartRef, Bodies, LocalDefs0},
    DefineOrder),
  {S, B}.

-spec define_remaining(#{type() => type_descriptor()}) -> ok.
define_remaining(Bodies) ->
  maps:foreach(
    fun(Ref, Body) ->
      case is_defined(Ref) of
        true -> ok;
        false -> define(Ref, Body), ok
      end
    end, Bodies).

% Process one SCC: for each node, try to globally cons; if hit, redirect.
-spec process_scc([type()], #{type() => [type()]},
                  {type(), #{type() => type_descriptor()}, #{type_descriptor() => type()}}) ->
    {type(), #{type() => type_descriptor()}, #{type_descriptor() => type()}}.
process_scc(SCC, RevGraph, Acc) ->
  lists:foldl(
    fun(ToDefine, {StartRef, Bodies, LocalDefs}) ->
      case is_defined(ToDefine) of
        true ->
          % Could happen if our pre-allocated ID collided with prior state;
          % shouldn't, but be defensive.
          {StartRef, Bodies, LocalDefs};
        false ->
          case maps:find(ToDefine, Bodies) of
            error ->
              % Already redirected in an earlier iteration of this SCC.
              {StartRef, Bodies, LocalDefs};
            {ok, Body} ->
              case is_consed_local_or_global(Body, LocalDefs) of
                {true, ExistingNode} ->
                  redirect_to_existing(ToDefine, ExistingNode, StartRef, Bodies, LocalDefs, RevGraph);
                false ->
                  {StartRef, Bodies, LocalDefs#{Body => ToDefine}}
              end
          end
      end
    end, Acc, SCC).

-spec is_consed_local_or_global(type_descriptor(), #{type_descriptor() => type()}) ->
    {true, type()} | false.
is_consed_local_or_global(Body, LocalDefs) ->
  case is_consed(Body) of
    {true, N} -> {true, N};
    false ->
      case LocalDefs of
        #{Body := N} -> {true, N};
        _ -> false
      end
  end.

-spec redirect_to_existing(type(), type(), type(),
                           #{type() => type_descriptor()},
                           #{type_descriptor() => type()},
                           #{type() => [type()]}) ->
    {type(), #{type() => type_descriptor()}, #{type_descriptor() => type()}}.
redirect_to_existing(ToDefine, ExistingNode, StartRef, Bodies, LocalDefs, RevGraph) ->
  Bodies1 = maps:remove(ToDefine, Bodies),
  % Rewrite bodies that contained ToDefine to reference ExistingNode instead.
  ContainedIn = maps:get(ToDefine, RevGraph, []),
  Bodies2 = lists:foldl(
    fun(E, Acc) ->
      case maps:find(E, Acc) of
        error -> Acc;
        {ok, Val} ->
          NewVal = utils:replace(Val, #{ToDefine => ExistingNode}),
          Acc#{E => dnf_ty_variable:reorder(NewVal)}
      end
    end, Bodies1, ContainedIn),
  NewStartRef = case StartRef of ToDefine -> ExistingNode; _ -> StartRef end,
  {NewStartRef, Bodies2, LocalDefs}.

% Walk all reachable nodes; return a map keyed by ty_node of the ones whose
% transitive variable set intersects Dom (i.e. those that need a substituted copy).
-spec collect_needs_sub(type(), sets:set(variable())) -> #{type() => true}.
collect_needs_sub(Node, Dom) ->
  do_collect_needs_sub([Node], #{}, Dom, #{}).

-spec do_collect_needs_sub([type()], #{type() => boolean()}, sets:set(variable()), #{type() => true}) ->
    #{type() => true}.
do_collect_needs_sub([], _Visited, _Dom, Acc) -> Acc;
do_collect_needs_sub([N | Rest], Visited, Dom, Acc) ->
  case Visited of
    #{N := _} -> do_collect_needs_sub(Rest, Visited, Dom, Acc);
    _ ->
      Vars = all_variables(N),
      case sets:size(sets:intersection(Vars, Dom)) of
        0 ->
          do_collect_needs_sub(Rest, Visited#{N => true}, Dom, Acc);
        _ ->
          Body = load(N),
          Children = collect_node_refs(Body),
          do_collect_needs_sub(Rest ++ Children, Visited#{N => true}, Dom, Acc#{N => true})
      end
  end.

-spec collect_node_refs(type_descriptor()) -> [type()].
collect_node_refs(Body) ->
  utils:everything(
    fun(E = {node, Id}) when is_integer(Id) -> {ok, E}; (_) -> error end,
    Body).

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
%-spec opcache(term(), fun(() -> A)) -> A. % TODO scoped variables extension for annotations
-spec opcache(term(), fun(() -> type())) -> type().
opcache(Key, F) ->
  % process dict faster but we can't erase just parts of it, only everything
  case ets:lookup(?OPCACHE, Key) of
    [{_, Result}] -> ?assert_type(Result, type()); 
    [_ | _] -> error(invariant);
    [] ->
      R = F(),
      ets:insert(?OPCACHE, [{Key, R}]),
      R
  end.

-spec next_id() -> pos_integer().
next_id() ->
  NextId = ets:update_counter(?ID, id, 1),
  ?assert_type(NextId, pos_integer()).
