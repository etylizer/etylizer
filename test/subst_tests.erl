-module(subst_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tunion/1, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0]).
-import(test_utils, [is_subtype/2, is_equiv/2]).

eq_list(L1, L2) ->
  S1 = sets:from_list(L1),
  S2 = sets:from_list(L2),
  sets:is_subset(S1, S2) andalso sets:is_subset(S2, S1).

all_variables_fun_test() ->
  test_utils:reset_ets(),
  T = tfun_full([tvar('$0'), tvar('$1')], tvar('$2')),
  Ty = ast_lib:ast_to_erlang_ty(T),
  true = eq_list([ast_lib:ast_to_erlang_ty_var(V) || V <- [tvar('$0'), tvar('$1'), tvar('$2')]], ty_rec:all_variables(Ty)),
  ok.
