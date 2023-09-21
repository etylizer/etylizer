-module(dnf_var_predef).

-define(P, {ty_predef, ty_variable}).


-export([equal/2, compare/2]).


-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1, normalize/3, substitute/2]).

-export([var/1, predef/1,  all_variables/1, transform/2]).

-type variable() :: term(). % variable:type()
-type dnf_var_int() :: term().

predef(Predef) -> gen_bdd:terminal(?P, Predef).

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

eval(B) -> gen_bdd:eval(?P, B).
is_any(B) -> gen_bdd:is_any(?P, B).



% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).


% ==
% Emptiness for variable interval DNFs
% ==

is_empty(0) -> true;
is_empty({terminal, Interval}) ->
  ty_interval:is_empty(Interval);
is_empty({node, _Variable, PositiveEdge, NegativeEdge}) ->
  is_empty(PositiveEdge)
    andalso is_empty(NegativeEdge).


normalize(Ty, Fixed, M) -> normalize(Ty, [], [], Fixed, M).

normalize(0, _, _, _, _) -> [[]]; % satisfiable
normalize({terminal, Predef}, PVar, NVar, Fixed, M) ->
  ty_predef:normalize(Predef, PVar, NVar, Fixed, M);
normalize({node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  constraint_set:merge_and_meet(
    normalize(PositiveEdge, [Variable | PVar], NVar, Fixed, M),
    normalize(NegativeEdge, PVar, [Variable | NVar], Fixed, M)
  ).


substitute(T, M) -> substitute(T, M, [], []).

substitute(0, _, _, _) -> 0;
substitute({terminal, Interval}, Map, Pos, Neg) ->
  AllPos = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      ty_rec:pi(predef, Substitution)
    end, Pos),
  AllNeg = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      NewNeg = ty_rec:negate(Substitution),
      ty_rec:pi(predef, NewNeg)
    end, Neg),

  lists:foldl(fun(Current, All) -> intersect(Current, All) end, predef(Interval), AllPos ++ AllNeg);

substitute({node, Variable, PositiveEdge, NegativeEdge}, Map, P, N) ->

  LBdd = substitute(PositiveEdge, Map, [Variable | P], N),
  RBdd = substitute(NegativeEdge, Map, P, [Variable | N]),

  union(LBdd, RBdd).

all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
  [Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).

transform(0, #{empty := E}) -> E();
transform({terminal, Predef}, Ops) ->
  ty_predef:transform(Predef, Ops);
transform({node, Variable, PositiveEdge, NegativeEdge},
    Ops = #{negate := Negate, var := ToVar, union := Union, intersect := Intersect}) ->
  AstVar = ToVar(Variable),
  Union([
    Intersect([AstVar, transform(PositiveEdge, Ops)]),
    Intersect([Negate(AstVar), transform(NegativeEdge, Ops)])
  ]).
