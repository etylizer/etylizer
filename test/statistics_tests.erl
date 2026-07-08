-module(statistics_tests).

% Fixture-based regression tests that pin the statistics collectors' semantics,
% independent of the large paper corpora. Each test parses a small module in
% test_files/statistics/ and checks the collector output.
%
% The symbol table is left undefined (Ctx = {[], undefined}), so the
% symtab-dependent collectors (#7 call classification, #9 constraint shape) are
% skipped here; the raw/transformed-AST collectors are fully exercised.

-include_lib("eunit/include/eunit.hrl").
-include("etylizer_main.hrl").

-spec report(file:filename()) -> #{atom() => term()}.
report(File) ->
    global_state:with_new_state(
      fun() ->
          parse_cache:init(#opts{}),
          stdtypes:init(),
          try statistics:module_report(File, #opts{}, {[], undefined})
          after
              parse_cache:cleanup(),
              stdtypes:cleanup()
          end
      end).

fixture(Name) -> "test_files/statistics/" ++ Name.

-spec get(map(), [atom()]) -> term().
get(Map, [K]) -> maps:get(K, Map);
get(Map, [K | Rest]) -> get(maps:get(K, Map), Rest).

corpus_and_features_test() ->
    R = report(fixture("features.erl")),
    ?assertEqual(ok, maps:get(parse, R)),
    ?assertEqual(4, get(R, [corpus, n_functions])),
    ?assertEqual(3, get(R, [corpus, n_specced])),
    ?assertEqual(1, get(R, [corpus, n_unspecced])),
    ?assertEqual(1, get(R, [features, union])),
    ?assertEqual(1, get(R, [features, overloaded])),
    ?assertEqual(1, get(R, [features, polymorphic])),
    ?assertEqual(2, get(R, [features, numeric])),
    ?assertEqual(0, get(R, [features, dynamic_direct])).

patterns_test() ->
    R = report(fixture("patterns.erl")),
    ?assertEqual(2, get(R, [patterns, pat_matches])),
    ?assertEqual(4, get(R, [patterns, branches])),
    ?assertEqual(3, get(R, [patterns, type_tests])),
    ?assertEqual(3, get(R, [patterns, tt_var])),
    ?assertEqual(2, get(R, [patterns, tt_bound])).

refinement_test() ->
    R = report(fixture("refinement.erl")),
    ?assertEqual(5, get(R, [refinement, total_funs])),
    ?assertEqual(1, get(R, [refinement, r1])),
    ?assertEqual(2, get(R, [refinement, r2])),
    ?assertEqual(1, get(R, [refinement, r3])),
    ?assertEqual(1, get(R, [refinement, r4])),
    ?assertEqual(4, get(R, [refinement, any])).

index_calls_test() ->
    R = report(fixture("indexcalls.erl")),
    ?assertEqual(3, get(R, [index_calls, element_setelement, literal])),
    ?assertEqual(2, get(R, [index_calls, element_setelement, non_literal])),
    ?assertEqual(2, get(R, [index_calls, lists_key, literal])),
    ?assertEqual(1, get(R, [index_calls, lists_key, non_literal])).

dynamic_indirect_test() ->
    R = report(fixture("dynindirect.erl")),
    ?assertEqual(1, get(R, [features, dynamic_direct])),
    ?assertEqual(2, get(R, [features, dynamic_indirect])),
    ?assertEqual(3, get(R, [corpus, n_specced])),
    ?assertEqual(0, get(R, [corpus, n_unspecced])).
