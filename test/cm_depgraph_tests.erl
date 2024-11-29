-module(cm_depgraph_tests).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

add_dependency_test() ->
    TestGraph = cm_depgraph:add_dependency("test.erl", "foo.erl", cm_depgraph:new()),
    ResultGraph = cm_depgraph:add_dependency("test.erl", "bar.erl", TestGraph),
    AllFiles = ["test.erl", "foo.erl", "bar.erl"],
    ExpectedGraph = {sets:from_list(AllFiles),
        #{"test.erl" => sets:from_list(["bar.erl", "foo.erl"])}},
    ?assertEqual(cm_depgraph:pretty_depgraph(ExpectedGraph),
        cm_depgraph:pretty_depgraph(ResultGraph)).

update_dep_graph_test() ->
    ExampleFilePath = "./test_files/referenced_modules/module1.erl",
    ?LOG_WARN("ExampleFilePath=~s", ExampleFilePath),
    RawForms = parse:parse_file_or_die(ExampleFilePath),
    Forms = ast_transform:trans(ExampleFilePath, RawForms),
    SearchPath = [{local, "./test_files/referenced_modules/", []}],
    ResultGraph = cm_depgraph:update_dep_graph(ExampleFilePath, Forms, SearchPath,
                    cm_depgraph:new()),
    ExpectedGraph =
        {sets:to_list(sets:from_list(["./test_files/referenced_modules/module1.erl",
            "./test_files/referenced_modules/module2.erl",
            "./test_files/referenced_modules/module3.erl",
            "./test_files/referenced_modules/module4.erl",
            "./test_files/referenced_modules/module5.erl"])),
            #{"./test_files/referenced_modules/module2.erl" => ["./test_files/referenced_modules/module1.erl"],
              "./test_files/referenced_modules/module3.erl" => ["./test_files/referenced_modules/module1.erl"],
              "./test_files/referenced_modules/module4.erl" => ["./test_files/referenced_modules/module1.erl"],
              "./test_files/referenced_modules/module5.erl" => ["./test_files/referenced_modules/module1.erl"]}
        },
    ?assertEqual(ExpectedGraph, cm_depgraph:pretty_depgraph(ResultGraph)).

find_dependent_files_test() ->
    TestGraph = cm_depgraph:add_dependency("test.erl", "foo.erl", cm_depgraph:new()),
    ResultGraph = cm_depgraph:add_dependency("test.erl", "bar.erl", TestGraph),
    Deps = cm_depgraph:find_dependent_files("test.erl", ResultGraph),

    ?assertEqual(["bar.erl", "foo.erl"], lists:sort(Deps)).

% cycles
