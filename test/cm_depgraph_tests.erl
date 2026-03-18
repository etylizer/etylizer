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

% The cached graph: a project in a temporary directory with main.erl as its only entry
% point, checked several times while its files change.

-define(MAIN, "-module(main).\n-export([f/0]).\n-spec f() -> integer().\n").

-spec with_project(fun((file:name()) -> ok)) -> ok.
with_project(Action) ->
    tmp:with_tmp_dir("depgraph", "root", delete,
        fun(Dir) ->
            utils:mkdirs(filename:join(Dir, "_build/default/lib")),
            write(Dir, "rebar.lock", ""),
            write(Dir, "main.erl", ?MAIN ++ "f() -> helper:g().\n"),
            write(Dir, "helper.erl", "-module(helper).\n-export([g/0]).\n-spec g() -> integer().\ng() -> 1.\n"),
            write(Dir, "newmod.erl", "-module(newmod).\n-export([h/0]).\n-spec h() -> integer().\nh() -> 2.\n"),
            Action(Dir)
        end).

-spec write(file:name(), file:name(), string()) -> ok.
write(Dir, Name, Content) -> ok = file:write_file(filename:join(Dir, Name), Content).

% the files that were checked
-spec check(file:name(), [{atom(), string()}]) -> [file:name()].
check(Dir, Defines) ->
    Opts = #opts{
        files = [filename:join(Dir, "main.erl")],
        project_root = Dir,
        mode = test_mode,
        defines = Defines
    },
    lists:sort([filename:basename(F) || {F, _} <- etylizer_main:doWork(Opts)]).

% a module that becomes reachable is checked in the same run
new_dependency_test_() ->
    {timeout, 45, fun() -> with_project(fun(Dir) ->
        ?assertEqual(["helper.erl", "main.erl"], check(Dir, [])),
        ?assertEqual([], check(Dir, [])),
        write(Dir, "main.erl", ?MAIN ++ "f() -> helper:g() + newmod:h().\n"),
        ?assertEqual(["main.erl", "newmod.erl"], check(Dir, [])),
        ?assertEqual([], check(Dir, []))
    end) end}.

deleted_module_test_() ->
    {timeout, 45, fun() -> with_project(fun(Dir) ->
        ?assertEqual(["helper.erl", "main.erl"], check(Dir, [])),
        ok = file:delete(filename:join(Dir, "helper.erl")),
        write(Dir, "main.erl", ?MAIN ++ "f() -> 1.\n"),
        ?assertEqual(["main.erl"], check(Dir, [])),
        ?assertEqual([], check(Dir, []))
    end) end}.

% the graph of other options is not used
changed_define_test_() ->
    {timeout, 45, fun() -> with_project(fun(Dir) ->
        write(Dir, "main.erl",
            ?MAIN ++ "-ifdef(WITH_NEW).\nf() -> newmod:h().\n-else.\nf() -> helper:g().\n-endif.\n"),
        ?assertEqual(["helper.erl", "main.erl"], check(Dir, [])),
        ?assertEqual(["main.erl", "newmod.erl"], check(Dir, [{'WITH_NEW', "true"}]))
    end) end}.

load_depgraph_test() ->
    tmp:with_tmp_dir("depgraph", "root", delete,
        fun(Dir) ->
            Src = utils:normalize_path(filename:join(Dir, "a.erl")),
            File = filename:join(Dir, "depgraph"),
            ok = file:write_file(Src, "-module(a).\n"),
            Graph = cm_depgraph:new([Src]),
            ok = cm_depgraph:save_depgraph(File, key, Graph),
            ?assertEqual({ok, Graph, []}, cm_depgraph:load_depgraph(File, key)),
            ?assertEqual(stale, cm_depgraph:load_depgraph(File, other_key)),
            ok = file:write_file(Src, "-module(a).\n-export([f/0]).\nf() -> 1.\n"),
            ?assertEqual({ok, Graph, [Src]}, cm_depgraph:load_depgraph(File, key)),
            ok = file:delete(Src),
            ?assertEqual(stale, cm_depgraph:load_depgraph(File, key))
        end).
