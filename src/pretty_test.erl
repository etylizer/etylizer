-module(pretty_test).

-include_lib("eunit/include/eunit.hrl").
-include_lib("log.hrl").

pretty_ty_test() ->
    T = {tuple, [{predef, integer},
                 {singleton, 4},
                 {union, [{map, [{map_field_opt, {singleton, key}, {predef_alias, term}}]},
                          {fun_full,
                           [{predef_alias, string}, {list, {var, 'T'}}],
                           {named, {loc, "file.erl", 13, 9}, {ref, doc, 0}, []}}]}]},
    Doc = pretty:ty(T),
    S = pretty:render(Doc),
    ?assertEqual("{integer(), 4, #{key => term()} | fun((string(), [T]) -> doc())}", S).
