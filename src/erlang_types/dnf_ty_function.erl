-module(dnf_ty_function).

-define(ATOM, ty_function).
-define(LEAF, ty_bool).
-define(NODE, ty_node).

-export([
  unparse_any/0,
  unparse_any/1
]).

-include("dnf/bdd.hrl").

-spec is_empty_line({[T], [T], ?LEAF:type()}, T) -> {boolean(), T} when T :: ?ATOM:type().
is_empty_line({AllPos, Neg, T}, ST) ->
  T = ?LEAF:any(), % sanity
  % continue searching for any arrow ∈ N such that the line becomes empty
  lists:foldl(
    fun
      (_NegatedFun, {true, ST0}) -> {true, ST0}; 
      (NegatedFun, {false, ST0}) -> is_empty_cont(AllPos, NegatedFun, ST0) 
    end, 
    {false, ST}, 
    Neg
  ).

-spec is_empty_cont([T], T, ST) -> {boolean(), ST} when T :: ?ATOM:type().
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
-spec explore_function(Ty, Ty, [?ATOM:type()], S) -> {boolean(), S} when Ty :: ty_node:type().
explore_function(_T1, _T2, [], ST) -> {true, ST};
explore_function(T1, T2, [Function | Ps], ST0) ->
  {S1, S2} = {ty_function:domain(Function), ty_function:codomain(Function)},
  maybe 
    {true, ST1} ?= phi(T1, ?NODE:intersect(T2, S2), Ps, ST0),
    phi(?NODE:difference(T1, S1), T2, Ps, ST1)
  end.

-spec phi(Ty, Ty, [?ATOM:type()], S) -> {boolean(), S} when Ty :: ty_node:type().
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

-spec normalize_line({[T], [T], ?LEAF:type()}, monomorphic_variables(), T) -> {set_of_constraint_sets(), T} when T :: ?ATOM:type().
normalize_line({Pos, Neg, T}, Fixed, ST) ->
  T = ?LEAF:any(), % sanity
  S = lists:foldl(fun ty_node:union/2, ty_node:empty(), [ty_function:domain(FF) || FF <- Pos]),
  normalize_line_cont(S, Pos, Neg, Fixed, ST).

% -spec domains_to_tuple([T]) -> T when T :: ty:type().
% domains_to_tuple(Domains) ->
%   ty_node:make(dnf_ty_variable:leaf(ty_rec:tuples(ty_tuples:singleton(length(Domains), dnf_ty_tuple:singleton(ty_tuple:tuple(Domains)))))).

-spec normalize_line_cont(ty_node:type(), [T], [T], monomorphic_variables(), ST) -> {set_of_constraint_sets(), ST} when T :: ?ATOM:type().
normalize_line_cont(_, _, [], _Fixed, ST) -> {[], ST}; % non-empty
normalize_line_cont(S, P, [Function | N], Fixed, ST) ->
  T1 = ty_function:domain(Function),
  T2 = ty_function:codomain(Function),

  %% ∃ T1-->T2 ∈ N s.t.
  %%   T1 is in the domain of the function
  %%   S is the union of all domains of the positive function intersections
  {X1, ST0} = ty_node:normalize(ty_node:intersect(T1, ty_node:negate(S)), Fixed, ST),

  %io:format(user,"Exploring: ~p~n~p~n", [ty_node:dump(T1), ty_node:dump(ty_node:negate(T2))]),
  {X2, ST1} = explore_function_norm(T1, ty_node:negate(T2), P, Fixed, ST0),

  R1 = constraint_set:meet(X1, X2, Fixed),

  {R2, ST2} = normalize_line_cont(S, P, N, Fixed, ST1),

  % Continue searching for another arrow ∈ N
  {constraint_set:join(R1, R2, Fixed), ST2}.


-spec explore_function_norm(ty_node:type(), ty_node:type(), [T], monomorphic_variables(), S) -> {set_of_constraint_sets(), S} when T :: ?ATOM:type().
explore_function_norm(BigT1, T2, [], Fixed, ST0) ->
  {NT1, ST1} = ty_node:normalize(BigT1, Fixed, ST0),
  {NT2, ST2} = ty_node:normalize(T2, Fixed, ST1),
  {constraint_set:join(NT1, NT2, Fixed), ST2};
explore_function_norm(T1, T2, [Function | P], Fixed, ST0) ->
  {NT1, ST1} = ty_node:normalize(T1, Fixed, ST0),
  {NT2, ST2} = ty_node:normalize(T2, Fixed, ST1),

  S1 = ty_function:domain(Function),
  S2 = ty_function:codomain(Function),

  {NS1, ST3} = explore_function_norm(T1, ty_node:intersect(T2, S2), P, Fixed, ST2),
  {NS2, ST4} = explore_function_norm(ty_node:difference(T1, S1), T2, P, Fixed, ST3),

  {constraint_set:join(NT1,
    constraint_set:join(NT2,
      constraint_set:meet(NS1, NS2, Fixed), Fixed), Fixed), ST4}.

-spec all_variables_line([T], [T], ?LEAF:type(), cache()) -> sets:set(variable()) when T :: ?ATOM:type().
all_variables_line(P, N, Leaf, Cache) ->
  Leaf = ty_bool:any(),
  sets:union(
     [ty_function:all_variables(F, Cache) || F <- P]
  ++ [ty_function:all_variables(F, Cache) || F <- N]
  ).

unparse_any() -> {fun_simple}.
unparse_any(Size) ->
  {fun_full, [{predef, empty} || _ <- lists:seq(1, Size)], {predef, any}}.
