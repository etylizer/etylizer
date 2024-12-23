-module(constr_gen_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("kernel/include/logger.hrl").

-spec pat_guard_lower_upper_test() -> ok.
pat_guard_lower_upper_test() ->
    Symtab = symtab:empty(),
    % The guarded pattern `_ when true`
    Loc = ast:loc_auto(),
    P = {wildcard, Loc},
    G = [{'atom', Loc, true}],
    E = {var, Loc, {local_ref, {foo, 1}}},
    {Upper, Lower} = constr_gen:pat_guard_lower_upper(Symtab, P, [G], E),
    ?LOG_WARNING("Upper: ~w, Lower: ~w", [Upper, Lower]),
    % Upper and Lower should be equiv to any()
    Any = {predef, any},
    ?assertEqual(true, test_utils:is_equiv(Upper, Any)),
    ?assertEqual(true, test_utils:is_equiv(Lower, Any)).

-spec assert_ty_of_pat(ast:pat(), ast:ty(), ast:ty()) -> ok.
assert_ty_of_pat(P, Upper, Lower) ->
    Symtab = symtab:empty(),
    Env = #{},
    GivenUpper = constr_gen:ty_of_pat(Symtab, Env, P, upper),
    GivenLower = constr_gen:ty_of_pat(Symtab, Env, P, lower),
    ?LOG_WARNING("ty_of_pat, P=~200p, Upper=~w, GivenUpper=~w, Lower=~w, GivenLower=~w",
        [P, Upper, GivenUpper, Lower, GivenLower]),
    ?assertEqual(true, test_utils:is_equiv(Upper, GivenUpper)),
    ?assertEqual(true, test_utils:is_equiv(Lower, GivenLower)).


-spec ty_of_pat_list_test() -> ok.
ty_of_pat_list_test() ->
    Loc = ast:loc_auto(),
    Pnil = {nil, Loc},
    Pa = {'atom', Loc, a},
    Pb = {'atom', Loc, b},
    Pwild =  {wildcard, Loc},
    PCons1 = {cons, Loc, Pa, Pnil}, % pattern [a | []]
    PCons2 = {cons, Loc, Pa, Pwild}, % pattern [a | _]
    PCons3 = {cons, Loc, Pb, PCons2}, % pattern [b | a | _]
    PCons4 = {cons, Loc, Pb, PCons1}, % pattern [b | a | []]
    Tempty_list = stdtypes:tempty_list(),
    Ta = stdtypes:tatom(a),
    Tb = stdtypes:tatom(b),
    Tany = stdtypes:any(),
    Tbottom = stdtypes:empty(),
    assert_ty_of_pat(Pnil, Tempty_list, Tempty_list),
    assert_ty_of_pat(Pa, Ta, Ta),
    assert_ty_of_pat(Pwild, Tany, Tany),
    assert_ty_of_pat(PCons1, stdtypes:tnonempty_list(Ta), Tbottom),
    assert_ty_of_pat(PCons3, stdtypes:tnonempty_list(Tany), Tbottom),
    assert_ty_of_pat(PCons4, stdtypes:tnonempty_list(ast_lib:mk_union([Ta, Tb])), Tbottom),
    assert_ty_of_pat(PCons2, stdtypes:tnonempty_list(Tany), stdtypes:tnonempty_list(Ta)).
