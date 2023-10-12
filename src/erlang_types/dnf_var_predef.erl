-module(dnf_var_predef).

-define(P, {ty_predef, ty_variable}).


-export([equal/2, compare/2]).


-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/3, substitute/4]).

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

is_any(B) -> gen_bdd:is_any(?P, B).
is_empty(TyBDD) -> gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> ty_predef:is_empty(T).


% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

substitute(MkTy, T, M, _) -> gen_bdd:substitute(?P, MkTy, T, M, sets:new()).


normalize(Ty, Fixed, M) -> normalize(Ty, [], [], Fixed, M).

normalize({terminal, 0}, _, _, _, _) -> [[]]; % satisfiable
normalize({terminal, Predef}, PVar, NVar, Fixed, M) ->
  ty_predef:normalize(Predef, PVar, NVar, Fixed, M);
normalize({node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  constraint_set:merge_and_meet(
    normalize(PositiveEdge, [Variable | PVar], NVar, Fixed, M),
    normalize(NegativeEdge, PVar, [Variable | NVar], Fixed, M)
  ).


all_variables({terminal, 0}) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
  [Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).

transform({terminal, 0}, #{empty := E}) -> E();
transform({terminal, Predef}, Ops) ->
  ty_predef:transform(Predef, Ops);
transform({node, Variable, PositiveEdge, NegativeEdge},
    Ops = #{negate := Negate, var := ToVar, union := Union, intersect := Intersect}) ->
  AstVar = ToVar(Variable),
  Union([
    Intersect([AstVar, transform(PositiveEdge, Ops)]),
    Intersect([Negate(AstVar), transform(NegativeEdge, Ops)])
  ]).
