-module(dnf_var_int).

-define(ELEMENT, ty_variable).
-define(TERMINAL, ty_interval).

-export([is_empty/1, normalize/3, substitute/4]).
-export([var/1, int/1, all_variables/1, transform/2, apply_to_node/3, to_singletons/1]).

-include("bdd_var.hrl").

int(Interval) -> terminal(Interval).
var(Var) -> node(Var).

% partially generic
is_empty(TyBDD) -> dnf( TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> ty_interval:is_empty(T).

normalize(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, Atom) -> ty_interval:normalize(Atom, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% not recursive, no op substitution
apply_to_node(Node, _StdMap, _Memo) ->
  Node.

to_singletons(TyBDD) -> dnf(TyBDD, {
  fun(_, _, T) -> ty_interval:to_singletons(T) end,
  fun(L, R) ->
    {ExceptL, SinglesL} = L(),
    {ExceptR, SinglesR} = R(),
    Singles = ty_interval:diff(SinglesL ++ SinglesR, ty_interval:intersect(ExceptL, ExceptR)),
    Sequences = lists:flatten([lists:seq(A, B) || {range, A, B} <- Singles]),
    {[], [ty_rec:interval(dnf_var_int:int(ty_interval:interval(X, X))) || X <- Sequences]}
  end
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

  false = dnf_var_int:is_empty(Bdd),

  ok.

-endif.
