-module(dnf_var_int).

-define(P, {ty_interval, ty_variable}).

-export([equal/2, compare/2]).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/3, substitute/4]).
-export([var/1, int/1,  all_variables/1, transform/2, get_dnf/1]).

int(Interval) -> gen_bdd:terminal(?P, Interval).
var(Var) -> gen_bdd:element(?P, Var).

% generic
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).
union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).
is_any(B) -> gen_bdd:is_any(?P, B).
equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).
substitute(MkTy, T, M, Memo) -> gen_bdd:substitute(?P, MkTy, T, M, Memo).
all_variables(TyBDD) -> gen_bdd:all_variables(?P, TyBDD).
transform(Ty, Ops) -> gen_bdd:transform(?P, Ty, Ops).
get_dnf(Bdd) -> gen_bdd:get_dnf(?P, Bdd).

% partially generic
is_empty(TyBDD) -> gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> ty_interval:is_empty(T).

normalize(Ty, Fixed, M) -> gen_bdd:dnf(?P, Ty, {
  fun(Pos, Neg, Atom) -> ty_interval:normalize(Atom, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

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
