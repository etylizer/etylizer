-module(pretty_test).

-include_lib("eunit/include/eunit.hrl").

pretty_ty_test() ->
    T = {tuple, [{predef, integer},
                 {singleton, 4},
                 {union, [{map, [{map_field_opt, {singleton, key}, {predef_alias, term}}]},
                          {fun_full,
                           [{predef_alias, string}, {list, {var, 'T'}}],
                           {named, {loc, "file.erl", 13, 9}, {ty_ref, file, doc, 0}, []}}]}]},
    Doc = pretty:ty(T),
    S = pretty:render(Doc),
    ?assertEqual("{integer(),\n 4,\n #{key => term()} | fun((string(), list(T)) -> doc())}", S).

render_exps_test() ->
    L = {loc, "", 0, 0},
    Var = fun(Name) -> {var, L, {local_ref, {Name, 0}}} end,
    Render = fun(E) -> lists:flatten(pretty:render_exps([E], 0)) end,
    ?assertEqual("$a", Render({char, L, $a})),
    ?assertEqual("fun M:F/1", Render({fun_ref_dyn, L, {qref_dyn, Var('M'), Var('F'), {integer, L, 1}}})),
    ?assertEqual("fun (X) ->\n  X,\n  ok\nend",
                 Render({'fun', L, no_name, [{'X', 0}], [Var('X'), {atom, L, ok}]})).
