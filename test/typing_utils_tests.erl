-module(typing_utils_tests).

-include_lib("eunit/include/eunit.hrl").

make_dynamic_fun_env_test() ->
    Funs = [
        {function, dummy_loc, "foo", 2, []},
        {function, dummy_loc, "bar", 0, []}
    ],
    Env = typing_utils:make_dynamic_fun_env(Funs),
    ?assertEqual(
        {ty_scheme, [], {fun_full, [{dynamic}, {dynamic}], {dynamic}}},
        maps:get({ref, "foo", 2}, Env)
    ),
    ?assertEqual(
        {ty_scheme, [], {fun_full, [], {dynamic}}},
        maps:get({ref, "bar", 0}, Env)
    ).
