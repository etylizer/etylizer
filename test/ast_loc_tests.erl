-module(ast_loc_tests).

-include_lib("eunit/include/eunit.hrl").

to_loc_source_test() ->
    ?assertEqual({loc, "m.erl", 3, 7}, ast:to_loc("m.erl", erl_anno:new({3, 7}))).

to_loc_compiler_generated_test() ->
    Anno = erl_anno:set_generated(true, erl_anno:new({3, 7})),
    ?assertEqual({generated, compiler, {loc, "m.erl", 3, 7}}, ast:to_loc("m.erl", Anno)).

generated_test() ->
    Src = {loc, "m.erl", 3, 7},
    Gen = ast:generated(fun_clauses, ast:generated(compiler, Src)),
    ?assertEqual(fun_clauses, ast:generated_by(Gen)),
    ?assertEqual(none, ast:generated_by(Src)),
    ?assert(ast:is_generated_by(fun_clauses, Gen)),
    ?assert(ast:is_generated_by(compiler, Gen)),
    ?assertNot(ast:is_generated_by(match, Gen)),
    ?assertNot(ast:is_generated_by(compiler, Src)),
    ?assertNot(ast:is_generated_by(compiler, {internal, test})),
    ?assertEqual(Src, ast:source_loc(Gen)),
    ?assertEqual(none, ast:source_loc({internal, test})),
    ?assertEqual("m.erl:3:7", ast:format_loc(Gen)),
    ?assertEqual("internal:test", ast:format_loc({internal, test})).

is_loc_test() ->
    ?assert(ast:is_loc({loc, "m.erl", 3, 7})),
    ?assert(ast:is_loc({generated, match, {loc, "m.erl", 3, 7}})),
    ?assert(ast:is_loc({internal, test})),
    ?assertNot(ast:is_loc({generated, match, foo})),
    ?assertNot(ast:is_loc({tuple, {loc, "m.erl", 3, 7}, []})).

leq_loc_test() ->
    L1 = {loc, "m.erl", 3, 7},
    L2 = {loc, "m.erl", 4, 1},
    ?assert(ast:leq_loc(L1, ast:generated(match, L2))),
    ?assertNot(ast:leq_loc(ast:generated(match, L2), L1)),
    ?assert(ast:leq_loc({internal, test}, L1)),
    ?assertEqual(L1, ast:min_loc(ast:generated(match, L2), L1)).
