-module(dnf_ty_function).

-compile([export_all, nowarn_export_all]).

-define(ATOM, ty_function).
-define(LEAF, ty_bool).
-define(NODE, ty_node).

-define(F(Z), fun() -> Z end).

-include("dnf/bdd.hrl").

-type type() :: any(). % TODO
% -spec function(ty_function()) -> dnf_ty_function().
% function(TyFunction) -> node(TyFunction).

% -> {boolean(), local_cache()}.
is_empty_line({AllPos, Neg, _T}, ST) ->
  _T = ?LEAF:any(), % sanity
  % continue searching for any arrow ∈ N such that the line becomes empty
  lists:foldl(
    fun
      (_NegatedFun, {true, ST0}) -> {true, ST0}; 
      (NegatedFun, {false, ST0}) -> is_empty_cont(AllPos, NegatedFun, ST0) 
    end, 
    {false, ST}, 
    Neg
  ).

% -> {boolean(), local_cache()}.
is_empty_cont(Ps, NegatedFun, ST0) ->
  %% ∃ Ts-->T2 ∈ N s.t.
  %%    Ts is in the domains of the function
  T1 = ty_function:domain(NegatedFun),

  AllDomains = lists:map(fun ty_function:domain/1, Ps),
  Disj = ?NODE:disjunction(AllDomains),
  maybe 
    {true, ST1} ?= ?NODE:leq(T1, Disj, ST0),
    NegatedCodomain = ?NODE:negate(ty_function:codomain(NegatedFun)),
    explore_function(T1, NegatedCodomain, Ps, ST1)
  end.

% optimized phi' (4.10) from paper covariance and contravariance
% justification for this version of phi can be found in `prop_phi_function.erl`
%-spec explore_function(ty_ref(), ty_ref(), [term()]) -> boolean().
explore_function(_T1, _T2, [], ST) ->
  {true, ST};
explore_function(T1, T2, [Function | Ps], ST0) ->
  {S1, S2} = {ty_function:domain(Function), ty_function:codomain(Function)},
  maybe 
    {true, ST1} ?= phi(T1, ?NODE:intersect(T2, S2), Ps, ST0),
    phi(?NODE:difference(T1, S1), T2, Ps, ST1)
  end.

phi(T1, T2, [], ST0) ->
  maybe
    {false, ST1} ?= ?NODE:is_empty(T1, ST0),
    ?NODE:is_empty(T2, ST1)
  end;
phi(T1, T2, [Function | Ps], ST0) ->
  {S1, S2} = {ty_function:domain(Function), ty_function:codomain(Function)},
  maybe 
    {false, ST1} ?= ?NODE:is_empty(T1, ST0),
    {false, ST2} ?= ?NODE:is_empty(T2, ST1),
    maybe
      {true, ST4} ?= maybe
        {false, ST3} ?= ?NODE:leq(T1, S1, ST2),
        Codomains = lists:map(fun ty_function:codomain/1, Ps),
        Conj = ?NODE:conjunction(Codomains),
        ?NODE:leq(Conj, ?NODE:negate(T2), ST3)
      end,
      {true, ST5} ?= phi(T1, ?NODE:intersect(T2, S2), Ps, ST4),
      phi(?NODE:difference(T1, S1), T2, Ps, ST5)
    end
  end.

normalize_line({Pos, Neg, _T}, Fixed, ST) ->
  _T = ?LEAF:any(), % sanity
  %io:format(user, "[function] Normalizing ~p~n", [{Pos, Neg}]),

  S = lists:foldl(fun ty_node:union/2, ty_node:empty(), [ty_function:domain(FF) || FF = {ty_function, Refs, _} <- Pos]),
  %io:format(user, "All positive domains~n~p~n", [ty_node:dump(S)]),

  normalize_line_cont(S, Pos, Neg, Fixed, ST).

% -> ty_node()
domains_to_tuple(Domains) ->
  ty_node:make(dnf_ty_variable:leaf(ty_rec:tuples(ty_tuples:singleton(length(Domains), dnf_ty_tuple:singleton(ty_tuple:tuple(Domains)))))).

normalize_line_cont(_, _, [], _Fixed, ST) -> {[], ST}; % non-empty
normalize_line_cont(S, P, [Function | N], Fixed, ST) ->
  T1 = ty_function:domain(Function),
  T2 = ty_function:codomain(Function),

  %% ∃ T1-->T2 ∈ N s.t.
  %%   T1 is in the domain of the function
  %%   S is the union of all domains of the positive function intersections
  {X1, ST0} = ty_node:normalize(ty_node:intersect(T1, ty_node:negate(S)), Fixed, ST),

  %io:format(user,"Exploring: ~p~n~p~n", [ty_node:dump(T1), ty_node:dump(ty_node:negate(T2))]),
  {X2, ST1} = explore_function_norm_corec(T1, ty_node:negate(T2), P, Fixed, ST0),

  R1 = constraint_set:meet(X1, X2),

  {R2, ST2} = normalize_line_cont(S, P, N, Fixed, ST1),

  % Continue searching for another arrow ∈ N
  {constraint_set:join(R1, R2), ST2}.


% obs1: NT2 is [[]] more often than NT1, but both take <1ms
explore_function_norm_corec(BigT1, T2, [], Fixed, ST0) ->
  %T0 = os:system_time(millisecond),
  {NT1, ST1} = ty_node:normalize(BigT1, Fixed, ST0),
  {NT2, ST2} = ty_node:normalize(T2, Fixed, ST1),
  %case NT2 of [[]] -> io:format(user,"X~n~p~n~p~n~n~n", [NT1, constraint_set:join(NT1, NT2)]); _ -> ok end,
  %case NT2 of [[]] -> error(todo); _ -> ok end,
  %io:format(user,"~p~n",[os:system_time(millisecond) - T0]),
  {constraint_set:join(NT1, NT2), ST2};
% obs2: meet(NS1, NS2) is [[]] more often than NT1, but the checks for NT1 and NT2 are fast
explore_function_norm_corec(T1, T2, [Function | P], Fixed, ST0) ->
  Tx0 = os:system_time(millisecond),
  {NT1, ST1} = ty_node:normalize(T1, Fixed, ST0),
  {NT2, ST2} = ty_node:normalize(T2, Fixed, ST1),
  % case NT1 of [[]] -> error(todo); _ -> ok end,
  % case NT2 of [[]] -> error(todo); _ -> ok end,
  Tx1 = os:system_time(millisecond),

  S1 = ty_function:domain(Function),
  S2 = ty_function:codomain(Function),

  T0 = os:system_time(millisecond),
  {NS1, ST3} = explore_function_norm_corec(T1, ty_node:intersect(T2, S2), P, Fixed, ST2),
  {NS2, ST4} = explore_function_norm_corec(ty_node:difference(T1, S1), T2, P, Fixed, ST3),
  % io:format(user,"~p VS ~p~n",[Tx1 - Tx0, os:system_time(millisecond) - T0]),

  % case NT1 of [] -> error(todo); _ -> ok end,
  % case NT2 of [] -> error(todo); _ -> ok end,
  % case constraint_set:meet(NS1, NS2) of [[]] -> error(todo); _ -> ok end,

  {constraint_set:join(NT1,
    constraint_set:join(NT2,
      constraint_set:meet(NS1, NS2))), ST4}.
