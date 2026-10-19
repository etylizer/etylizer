-module(cm_depgraph_tests).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").
-include("etylizer_main.hrl").

add_dependency_test() ->
    TestGraph = cm_depgraph:add_dependency("test.erl", "foo.erl", cm_depgraph:new()),
    ResultGraph = cm_depgraph:add_dependency("test.erl", "bar.erl", TestGraph),
    AllFiles = ["test.erl", "foo.erl", "bar.erl"],
    ExpectedGraph = {
        sets:to_list(sets:from_list(AllFiles, [{version, 2}])),
        #{"test.erl" => sets:to_list(sets:from_list(["bar.erl", "foo.erl"], [{version, 2}]))}
    },
    ?assertEqual(ExpectedGraph,
        cm_depgraph:pretty_depgraph(ResultGraph)).

update_dep_graph_test() ->
    parse_cache:with_cache(#opts{}, fun() ->
        ExampleFilePath = "./test_files/referenced_modules/module1.erl",
        ?LOG_WARN("ExampleFilePath=~s", ExampleFilePath),
        RawForms = parse:parse_file_or_die(ExampleFilePath),
        Forms = ast_transform:trans(ExampleFilePath, RawForms),
        SearchPath = [{local, "./test_files/referenced_modules/", []}],
        ResultGraph = cm_depgraph:update_dep_graph(ExampleFilePath, Forms, SearchPath,
                        cm_depgraph:new()),
        ExpectedGraph =
            {sets:to_list(sets:from_list(["test_files/referenced_modules/module1.erl",
                "test_files/referenced_modules/module2.erl",
                "test_files/referenced_modules/module3.erl",
                "test_files/referenced_modules/module4.erl",
                "test_files/referenced_modules/module5.erl"], [{version, 2}])),
                #{"test_files/referenced_modules/module2.erl" => ["test_files/referenced_modules/module1.erl"],
                "test_files/referenced_modules/module3.erl" => ["test_files/referenced_modules/module1.erl"],
                "test_files/referenced_modules/module4.erl" => ["test_files/referenced_modules/module1.erl"],
                "test_files/referenced_modules/module5.erl" => ["test_files/referenced_modules/module1.erl"]}
            },
        ?assertEqual(ExpectedGraph, cm_depgraph:pretty_depgraph(ResultGraph))
    end).

find_dependent_files_test() ->
    TestGraph = cm_depgraph:add_dependency("test.erl", "foo.erl", cm_depgraph:new()),
    ResultGraph = cm_depgraph:add_dependency("test.erl", "bar.erl", TestGraph),
    Deps = cm_depgraph:find_dependent_files("test.erl", ResultGraph),

    ?assertEqual(["bar.erl", "foo.erl"], lists:sort(Deps)).

% cycles

-define(MAIN, "-module(main).\n-export([f/0]).\n-spec f() -> integer().\n").

-spec write(file:name(), file:name(), string()) -> ok.
write(Dir, Name, Content) -> ok = file:write_file(filename:join(Dir, Name), Content).

-spec check(file:name(), [{atom(), string()}]) -> [file:name()].
check(Dir, Defines) ->
    Opts = #opts{
        files = [filename:join(Dir, "main.erl")],
        project_root = Dir,
        defines = Defines
    },
    lists:sort([filename:basename(F) || F <- etylizer_main:doWork(Opts)]).

cached_test_() ->
    {timeout, 45, fun() -> tmp:with_tmp_dir("depgraph", "root", delete, fun(Dir) ->
        utils:mkdirs(filename:join(Dir, "_build/default/lib")),
        write(Dir, "rebar.lock", ""),
        write(Dir, "main.erl", ?MAIN ++ "-ifdef(WITH_NEW).\nf() -> newmod:h().\n-else.\nf() -> 1.\n-endif.\n"),
        write(Dir, "helper.erl", "-module(helper).\n-export([g/0]).\n-spec g() -> integer().\ng() -> 1.\n"),
        write(Dir, "newmod.erl", "-module(newmod).\n-export([h/0]).\n-spec h() -> integer().\nh() -> 2.\n"),
        New = [{'WITH_NEW', "true"}],
        ?assertEqual(["main.erl"], check(Dir, [])),
        ?assertEqual(["main.erl", "newmod.erl"], check(Dir, New)),
        write(Dir, "main.erl", ?MAIN ++ "f() -> helper:g().\n"),
        ?assertEqual(["helper.erl", "main.erl"], check(Dir, New)),
        ok = file:delete(filename:join(Dir, "helper.erl")),
        write(Dir, "main.erl", ?MAIN ++ "f() -> 1.\n"),
        ?assertEqual(["main.erl"], check(Dir, New)),
        File = filename:join([Dir, "_etylizer", "depgraph"]),
        {ok, [{etylizer_depgraph, _, Key, _, Graph}]} = file:consult(File),
        ?assertMatch({ok, Graph, [], _}, cm_depgraph:load_depgraph(File, Key))
    end) end}.

header_test_() ->
    {timeout, 45, fun() -> tmp:with_tmp_dir("depgraph", "header", delete, fun(Dir) ->
        utils:mkdirs(filename:join(Dir, "_build/default/lib")),
        write(Dir, "rebar.lock", ""),
        write(Dir, "m.erl", "-module(m).\n-export([g/0]).\n-spec g() -> integer().\ng() -> 1.\n"),
        write(Dir, "h.hrl", "-define(V, 1).\n"),
        write(Dir, "main.erl", ?MAIN ++ "-include(\"h.hrl\").\nf() -> ?V.\n"),
        ?assertEqual(["main.erl"], check(Dir, [])),
        write(Dir, "h.hrl", "-define(V, m:g()).\n"),
        ?assertEqual(["m.erl", "main.erl"], check(Dir, [])),
        write(Dir, "m.erl", "-module(m).\n-export([g/0]).\n-spec g() -> atom().\ng() -> a.\n"),
        ?assertThrow({etylizer, ty_error, _}, check(Dir, []))
    end) end}.
