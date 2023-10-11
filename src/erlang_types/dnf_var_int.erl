-module(dnf_var_int).

-define(P, {ty_interval, ty_variable}).


-export([equal/2, compare/2]).


-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/3, substitute/2]).

-export([var/1, int/1,  all_variables/1, transform/2]).

-type interval() :: term(). % interval:type()
-type variable() :: term(). % variable:type()
-type dnf_var_int() :: term().

-spec int(interval()) -> dnf_var_int().
int(Interval) -> gen_bdd:terminal(?P, Interval).

-spec var(variable()) -> dnf_var_int().
var(Var) -> gen_bdd:element(?P, Var).

% ==
% type interface
% ==
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).

union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).

is_any(B) -> gen_bdd:is_any(?P, B).



% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).


% ==
% Emptiness for variable interval DNFs
% ==

is_empty({terminal, 0}) -> true;
is_empty({terminal, Interval}) ->
  ty_interval:is_empty(Interval);
is_empty({node, _Variable, PositiveEdge, NegativeEdge}) ->
  is_empty(PositiveEdge)
    andalso is_empty(NegativeEdge).


normalize(Ty, Fixed, M) -> normalize(Ty, [], [], Fixed, M).

normalize({terminal, 0}, _, _, _, _) -> [[]]; % satisfiable
normalize({terminal, Atom}, PVar, NVar, Fixed, M) ->
  ty_interval:normalize(Atom, PVar, NVar, Fixed, M);
normalize({node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  constraint_set:merge_and_meet(
    normalize(PositiveEdge, [Variable | PVar], NVar, Fixed, M),
    normalize(NegativeEdge, PVar, [Variable | NVar], Fixed, M)
  ).


substitute(T, M) -> substitute(T, M, [], []).

substitute({terminal, 0}, _, _, _) -> {terminal, 0};
substitute({terminal, Interval}, Map, Pos, Neg) ->
  AllPos = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      ty_rec:pi(interval, Substitution)
    end, Pos),
  AllNeg = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      NewNeg = ty_rec:negate(Substitution),
      ty_rec:pi(interval, NewNeg)
    end, Neg),

  lists:foldl(fun(Current, All) -> intersect(Current, All) end, int(Interval), AllPos ++ AllNeg);

substitute({node, Variable, PositiveEdge, NegativeEdge}, Map, P, N) ->

  LBdd = substitute(PositiveEdge, Map, [Variable | P], N),
  RBdd = substitute(NegativeEdge, Map, P, [Variable | N]),

  union(LBdd, RBdd).

all_variables({terminal, 0}) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
  [Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).

transform({terminal, 0}, #{empty := E}) -> E();
transform({terminal, Int}, Ops) ->
  ty_interval:transform(Int, Ops);
transform({node, Variable, PositiveEdge, NegativeEdge},
    Ops = #{negate := Negate, var := ToVar, union := Union, intersect := Intersect}) ->
  AstVar = ToVar(Variable),
  Union([
    Intersect([AstVar, transform(PositiveEdge, Ops)]),
    Intersect([Negate(AstVar), transform(NegativeEdge, Ops)])
  ]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  test_utils:reset_ets(),
  %   a1 ^ !a3 ^ 2-10
  % U a1 ^ 1-10
  % U !a2 ^ 5-8
  Ia = ty_interval:interval(2, 10),
  Ib = ty_interval:interval(1, 10),
  Ic = ty_interval:interval(5, 8),

  VarA = ty_variable:new("a1"),
  VarB = ty_variable:new("a2"),
  VarC = ty_variable:new("a3"),

  BIntA = dnf_var_int:int(Ia),
  BVar1 = dnf_var_int:var(VarA),
  BVar2 = dnf_var_int:var(VarB),
  BVar3 = dnf_var_int:var(VarC),
  BIntB = dnf_var_int:int(Ib),
  BIntC = dnf_var_int:int(Ic),

  U1 = dnf_var_int:intersect(dnf_var_int:intersect(BIntA, BVar1), dnf_var_int:negate(BVar3)),
  U2 = dnf_var_int:intersect(BVar1, BIntB),
  U3 = dnf_var_int:intersect(BIntC, dnf_var_int:negate(BVar2)),

  Bdd = dnf_var_int:union(dnf_var_int:union(U1, U2), U3),

%%  io:format(user, "~p~n", [Bdd]),
  false = dnf_var_int:is_empty(Bdd),

  ok.

compact_ints_test() ->
  test_utils:reset_ets(),
  %   1-5
  % U 6-10 -> 1-10
  Ia = ty_interval:interval(1, 5),
  Ib = ty_interval:interval(6, 10),

  BIntA = dnf_var_int:int(Ia),
  BIntB = dnf_var_int:int(Ib),

  Bdd = dnf_var_int:union(BIntA, BIntB),

%%  io:format(user, "~p~n", [Bdd]),
  false = dnf_var_int:is_empty(Bdd),

  ok.

-endif.

