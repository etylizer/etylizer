-module(variance_cache_tests).

-include_lib("eunit/include/eunit.hrl").

variance_cache_in_symtab_test() ->
    Key = {ty_key, m, t, 1},
    Tab = symtab:from_types(#{Key => {ty_scheme, [{a, {predef, any}}], {fun_full, [{var, a}], {predef, any}}}}),
    ?assertEqual(undefined, symtab:get_variances(Tab)),
    Cached = symtab:extend_symtab(".", [], Tab, symtab:empty()),
    ?assertEqual(#{Key => [contra]}, symtab:get_variances(Cached)),
    ?assertEqual(#{Key => [contra]},
                 symtab:get_variances(symtab:extend_symtab_with_fun_env(#{}, Cached))),
    ?assertEqual(undefined,
                 symtab:get_variances(symtab:extend_symtab_with_module_list(Cached, [], [], symtab:empty()))),
    ok.
