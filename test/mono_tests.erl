-module(mono_tests).

-include_lib("eunit/include/eunit.hrl").

-spec string_contains(string(), string()) -> boolean().
string_contains(Full, Search) -> string:str(Full, Search) > 0.

-spec check_mono_ty(ast:ty_scheme(), ast:ty() | [ast:ty()]| cyclic) -> ok.
check_mono_ty(Input, cyclic) ->
    try
        typing_common:mono_ty(ast:loc_auto(), Input, 0, symtab:empty()),
        ?assert(false, "expected exception")
    catch
        throw:{etylizer,ty_error, Msg} ->
            ?assert(string_contains(Msg, "Cyclic bounds in type spec"))
    end;
check_mono_ty(Input, Expected) ->
    {Given, _, _} = typing_common:mono_ty(ast:loc_auto(), Input, 0, symtab:empty()),
    if
        is_list(Expected) ->
            lists:any(fun (T) -> T =:= Given end, Expected);
        true ->
            ?assertEqual(Expected, Given)
    end.

mono_simple_test() ->
    check_mono_ty({ty_scheme, [], stdtypes:tint()}, stdtypes:tint()).

poly_simple_test() ->
    Any = stdtypes:tany(),
    check_mono_ty({ty_scheme, [{a, Any}], {var, a}}, {var, 'a#0'}),
    check_mono_ty({ty_scheme, [{a, Any}], {fun_full, [{var, a}], {var, a}}},
        {fun_full, [{var, 'a#0'}], {var, 'a#0'}}),
    check_mono_ty({ty_scheme, [{a, Any}, {b, Any}], {tuple, [{var, a}, {var, b}]}},
        [{tuple, [{var, 'a#0'}, {var, 'b#1'}]}, {tuple, [{var, 'a#1'}, {var, 'b#0'}]}]).

poly_bounded_simple_test() ->
    Int = stdtypes:tint(),
    check_mono_ty({ty_scheme, [{a, Int}], {var, a}}, Int),
    check_mono_ty({ty_scheme, [{a, Int}], {fun_full, [{var, a}], {var, a}}},
        {fun_full, [Int], Int}).

poly_bounded_chain_test() ->
    Int = stdtypes:tint(),
    check_mono_ty({ty_scheme, [{a, {var, b}}, {b, Int}], {tuple, [{var, a}, {var, b}]}},
        {tuple, [Int, Int]}),
    check_mono_ty({ty_scheme, [{b, Int}, {a, {var, b}}], {tuple, [{var, a}, {var, b}]}},
        {tuple, [Int, Int]}),
    check_mono_ty({ty_scheme, [{a, {var, b}}, {b, stdtypes:tany()}], {tuple, [{var, a}, {var, b}]}},
        {tuple, [{var, 'b#0'}, {var, 'b#0'}]}).

poly_bounded_cycle_test() ->
    check_mono_ty({ty_scheme, [{a, {var, b}}, {b, {var, a}}], {var, a}}, cyclic).
