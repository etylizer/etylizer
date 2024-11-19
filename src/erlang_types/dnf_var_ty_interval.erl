-module(dnf_var_ty_interval).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_interval).

-export([is_empty/1, normalize_corec/3, substitute/4]).
-export([var/1, int/1, all_variables/2, transform/2, apply_to_node/3, to_singletons/1]).

-include("bdd_var.hrl").

int(Interval) -> terminal(Interval).
var(Var) -> node(Var).

% partially generic
is_empty(TyBDD) -> dnf( TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_interval:is_empty(T).

normalize_corec(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, Atom) -> dnf_ty_interval:normalize_corec(Atom, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% not recursive, no op substitution
apply_to_node(Node, _StdMap, _Memo) ->
  Node.

to_singletons(TyBDD) -> dnf(TyBDD, {
  fun([], [], T) -> dnf_ty_interval:to_singletons(T); (_, _, _) -> [] end,
  fun erlang:'++'/2
}).


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  test_utils:reset_ets(),
  %   a1 ^ !a3 ^ 2-10
  % U a1 ^ 1-10
  % U !a2 ^ 5-8
  Ia = dnf_ty_interval:interval(2, 10),
  Ib = dnf_ty_interval:interval(1, 10),
  Ic = dnf_ty_interval:interval(5, 8),

  VarA = ty_variable:new(a1),
  VarB = ty_variable:new(a2),
  VarC = ty_variable:new(a3),

  BIntA = dnf_var_ty_interval:int(Ia),
  BVar1 = dnf_var_ty_interval:var(VarA),
  BVar2 = dnf_var_ty_interval:var(VarB),
  BVar3 = dnf_var_ty_interval:var(VarC),
  BIntB = dnf_var_ty_interval:int(Ib),
  BIntC = dnf_var_ty_interval:int(Ic),

  U1 = dnf_var_ty_interval:intersect(dnf_var_ty_interval:intersect(BIntA, BVar1), dnf_var_ty_interval:negate(BVar3)),
  U2 = dnf_var_ty_interval:intersect(BVar1, BIntB),
  U3 = dnf_var_ty_interval:intersect(BIntC, dnf_var_ty_interval:negate(BVar2)),

  Bdd = dnf_var_ty_interval:union(dnf_var_ty_interval:union(U1, U2), U3),

%%  io:format(user, "~p~n", [Bdd]),
  false = dnf_var_ty_interval:is_empty(Bdd),

  ok.

compact_ints_test() ->
  test_utils:reset_ets(),
  %   1-5
  % U 6-10 -> 1-10
  Ia = dnf_ty_interval:interval(1, 5),
  Ib = dnf_ty_interval:interval(6, 10),

  BIntA = dnf_var_ty_interval:int(Ia),
  BIntB = dnf_var_ty_interval:int(Ib),

  Bdd = dnf_var_ty_interval:union(BIntA, BIntB),

  false = dnf_var_ty_interval:is_empty(Bdd),

  ok.

-endif.
