-module(ty_node).

-compile([export_all, nowarn_export_all]).

-export_type([local_cache/0]).

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

% -record(ty_node, {id :: integer(), definition :: term()}).
-type type() :: any(). %TODO
-opaque local_cache() :: #{}. % TODO type cache is only allowed to be inspected in this module

compare({node, Id1}, {node, Id2}) when Id1 < Id2 -> lt;
compare({node, Id1}, {node, Id2}) when Id1 > Id2 -> gt;
compare({node, _Id1}, {node, _Id2}) -> eq;
% this is an architecture hack;
% ty_rec is used differently in ty_parser with local references
% ty_node has to support comparing these local temporary references
compare({local_ref, Id1}, {local_ref, Id2}) when Id1 < Id2 -> lt;
compare({local_ref, Id1}, {local_ref, Id2}) when Id1 > Id2 -> gt;
compare({local_ref, _Id1}, {local_ref, _Id2}) -> eq;
compare({local_ref, _}, {node, _}) -> lt;
compare({node, _}, {local_ref, _}) -> gt.

make(Ty) ->
  Res = ets:lookup(?UNIQUETABLE, Ty),
  case Res of
    [{_, Ref}] -> Ref;
    _ -> define(new_ty_node(), Ty)
  end.

is_consed(Ty) ->
  Res = ets:lookup(?UNIQUETABLE, Ty),
  case Res of
    [{Ty, Node}] -> {true, Node};
    _ -> false
  end.

is_defined(Node) ->
  Res = ets:lookup(?SYSTEM, Node),
  case Res of
    [{_, _}] -> true;
    _ -> false
  end.

new_ty_node() ->
  {node, next_id()}.

define(Reference, Node) ->
  [] = ets:lookup(?SYSTEM, Reference),
  [] = ets:lookup(?UNIQUETABLE, {Node, Reference}),
  ets:insert(?SYSTEM, {Reference, Node}),
  ets:insert(?UNIQUETABLE, {Node, Reference}),
  % io:format(user,"  +++++++++++++~nStore: ~p~n~p~n  +++++++++++++~n", [Reference, Node]),
  Reference.

next_id() ->
  NextId = ets:update_counter(?ID, id, 1),
  NextId.

load(TyNode) ->
  [{TyNode, Ty}] = ets:lookup(?SYSTEM, TyNode),
  Ty.
  
leq(T1, T2) ->
  is_empty(difference(T1, T2)).

leq(T1, T2, Cache) ->
  is_empty(difference(T1, T2), Cache).

-spec is_empty(type()) -> boolean().
is_empty(TyNode) ->
  T1 = os:system_time(microsecond),
  case ets:lookup(?CACHE, TyNode) of
    [{_, R}] -> 
      %io:format(user,"Cache: ~p us~n", [os:system_time(microsecond)-T1]),
      R;
    [] ->
      % TODO update global cache with local cache entries
      T0 = os:system_time(microsecond),
      {Result, LocalCache} = is_empty(TyNode, #{}),
      %io:format(user,"Empty ~p in ~p us~n", [TyNode, os:system_time(microsecond)-T0]),
      utils:update_ets_from_map(?CACHE, LocalCache),
      ets:insert(?CACHE, [{TyNode, Result}]),
      
      Result
  end.

% see Frisch PhD thesis
% TODO merge P and N into one ETS table
% TODO implement backtracking-free algorithm
-spec is_empty(type(), local_cache()) -> {boolean(), local_cache()}.
is_empty(TyNode, LocalCache) ->
  Ty = load(TyNode),

  case ets:lookup(?CACHE, Ty) of
    [{Ty, Result}] -> 
      {Result, LocalCache};
    [] ->
      case {{ok, ok}, LocalCache} of
        % {{#{Ty := false}, _}, _} -> 
        %   io:format(user,"X", []),
        %   {false, LocalCache}; % global cache hit
        % {{_, #{Ty := true}}, _} -> 
        %   io:format(user,"X", []),
        %   {true, LocalCache}; % global cache hit
        {{_, _}, #{Ty := Res}} -> 
          %case Res of false -> io:format(user, "x", []); _ -> ok end,
          % local cache hit
          {Res, LocalCache};
        _ -> 
          % assume type is empty and add to state
          % N U {t}
          {Result, LC_0} = ?TY:is_empty(Ty, LocalCache#{Ty => true}),

          case Result of 
            % empty; 
            % local cache can be kept as is 
            % Ty is empty is now cached, and all intermediate results are also cached
            true -> 
              {true, LC_0};

            % not empty;
            % invalidate all types that were assumed to be empty
            %  => recover initial N
            % and add Ty to be non-empty to the cache
            % we don't need to backtrack (there is no single global cache), 
            % use the LocalCache from the arguments
            false -> 
              {false, LocalCache#{Ty => false}}
          end
      end
  end.

negate(T) ->
  opcache({n, T}, fun() -> make(?TY:negate(load(T))) end).

intersect(T1, T2) ->
  opcache({i, T1, T2}, fun() -> make(?TY:intersect(load(T1), load(T2))) end).

union(T1, T2) ->
  opcache({u, T1, T2}, fun() -> make(?TY:union(load(T1), load(T2))) end).

difference(T1, T2) ->
  opcache({d, T1, T2}, fun() -> make(?TY:difference(load(T1), load(T2))) end).

opcache(Key, F) ->
  % process dict faster but we can't erase just parts of it, only everything
  % 0.43
  % case get(Key) of
  %   undefined ->
  %     Res = F(),
  %     put(Key, Res),
  %     Res;
  %   Z ->
  %     Z
  % end.
  % 0.56 seconds
  case ets:lookup(?OPCACHE, Key) of
    [{_, Result}] -> Result;
    [] ->
      R = F(),
      ets:insert(?OPCACHE, [{Key, R}]),
      R
  end.
  % 2.6 seconds
  % F().

any() ->
  make(?TY:any()).

empty() ->
  make(?TY:empty()).

disjunction(Nodes) ->
  lists:foldl(fun(E, Acc) -> union(E, Acc) end, empty(), Nodes).

conjunction(Nodes) ->
  lists:foldl(fun(E, Acc) -> intersect(E, Acc) end, any(), Nodes).

dump(Ty) ->
  do_dump([Ty], #{}).

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
% -spec normalize(type(), local_cache()) -> {term(), local_cache()}.
normalize(TyNode, FixedVariables) ->
  case ets:lookup(?NORMCACHE, {TyNode, FixedVariables}) of
    [{_, Result}] -> Result;
    [] ->
      % TODO can do global cache instead of just TyNode
      {Time, {Result, _LocalCache}} = timer:tc(fun() -> normalize(TyNode, FixedVariables, #{}) end),
      ets:insert(?NORMCACHE, [{{TyNode, FixedVariables}, Result}]),
      % io:format(user,"Normalize ~p in ~p us~n", [TyNode, Time]),
      Result
  end.

normalize(TyNode, FixedVariables, LocalCache) ->
  Ty = load(TyNode),

  case {{ok, ok}, LocalCache} of
    {{_, _}, #{{Ty, FixedVariables} := Res}} -> 
      % local cache hit
      %io:format(user, "X", []),
      {Res, LocalCache};
    _ -> 
      % assume type is normalized and add to local cache
      {Result, LC_0} = ?TY:normalize(Ty, FixedVariables, LocalCache#{{Ty, FixedVariables} => [[]]}),

      case Result of 
        % satisfiable; 
        % local cache can be kept as is 
        % Ty is empty is now cached, and all intermediate results are also cached
        [[]] -> 
          {[[]], LC_0};

        % not satisfiable;
        % invalidate all types that were assumed to be satisfiable
        %  => recover initial cache
        % and add the result of Ty to the cache
        Normalized -> 
          {Normalized, LocalCache#{{Ty, FixedVariables} => Normalized}}
      end
  end.

unparse(Node = {node, Id}, Cache) -> 
  case ty_parser:unparse_mapping(Node) of
    {hit, Result} -> {Result, Cache};
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
          {R, C0} = ?TY:unparse(Ty, NewCache),

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
substitute(Node, Varmap) ->
  % io:format(user,"Substitution: ~p with ~p~n", [Node, Varmap]),
  T1 = ty_parser:unparse(Node),
  Subst = #{begin {{var, Name}, _} = ty_variable:unparse(K, #{}), Name end => ty_parser:unparse(V) || K := V <- Varmap},
  % io:format(user,"Substitution: ~p with~n ~p~n", [T1, Subst]),
  Res = ty_parser:apply(Subst, T1, no_clean),
  NewNode = ty_parser:parse(Res),
  % io:format(user,"~p~n~p~n", [NewNode, dump(NewNode)]),
  NewNode.
