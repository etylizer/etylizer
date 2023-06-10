-module(cm_depgraph_tests).

-include_lib("eunit/include/eunit.hrl").

add_dependency_test() ->
    TestGraph = maps:put("test.erl", ["foo.erl"], maps:new()),
    ResultGraph = cm_depgraph:add_dependency("test.erl", "bar.erl", TestGraph),

    true = #{"test.erl" => ["bar.erl", "foo.erl"]} == ResultGraph.

update_dependency_graph_test() ->
    ExampleFilePath = "./test_files/export_modules/module1.erl",
    RawForms = parse:parse_file_or_die(ExampleFilePath),
    Forms = ast_transform:trans(ExampleFilePath, RawForms),
    SourcesList = ["./test_files/export_modules/module2.erl", "./test_files/export_modules/module3.erl"],
    ResultGraph = cm_depgraph:update_dependency_graph(ExampleFilePath, Forms, SourcesList, maps:new()),

    TargetGraph = #{"./test_files/export_modules/module2.erl" => ["./test_files/export_modules/module1.erl"],
                    "./test_files/export_modules/module3.erl" => ["./test_files/export_modules/module1.erl"]},

    true = TargetGraph == ResultGraph.

find_dependent_files_test() ->
    TestGraph = #{"test.erl" => ["bar.erl", "foo.erl"]},
    Dependencies = cm_depgraph:find_dependent_files("test.erl", TestGraph),

    true = ["bar.erl", "foo.erl"] == Dependencies.
