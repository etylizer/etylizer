-module(fungraph_tests).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

-spec fungraph_01_test() -> ok.
fungraph_01_test() ->
    F = "test_files/fungraph_test_mod.erl",
    RawForms = parse:parse_file_or_die(F),
    Forms = ast_transform:trans(F, RawForms),
    L = fungraph:dependency_order(Forms),
    NamesOnly =
        lists:map(fun (Set) ->
                          sets:from_list(lists:map(fun ast:get_fun_name/1, sets:to_list(Set)))
                  end, L),
    ?LOG_WARN("NamesOnly: ~p", lists:map(fun sets:to_list/1, NamesOnly)),
    ?assertEqual([sets:from_list(["spam/0"]),
                  sets:from_list(["foo/0", "bar/0", "with_spec/0"]),
                  sets:from_list(["egg/1"]),
                  sets:from_list(["buzz/0"])],
                 NamesOnly).
