-module(dnf_ty_variable).
-vsn({3,0,0}).

-define(P, {bdd_bool, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1, substitute/3]).

-export([variable/1, all_variables/1]).

variable(TyVariable) -> gen_bdd:element(?P, TyVariable).

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

is_empty(0) -> true;
is_empty({terminal, 1}) -> false;
is_empty({node, _TyVariable, L_BDD, R_BDD}) ->
  is_empty(L_BDD) andalso is_empty(R_BDD).


substitute(0, _, _) -> 0;
substitute({terminal, 1}, _, _) ->
  {terminal, 1};
substitute({node, TyVariable, L_BDD, R_BDD}, Map, Memo) ->
  error({implement, substitute, vardnf}).

all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, TyVariable, PositiveEdge, NegativeEdge}) ->
  [TyVariable]
    ++ all_variables(PositiveEdge)
    ++ all_variables(NegativeEdge).

