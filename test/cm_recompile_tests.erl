-module(cm_recompile_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("../src/ety_main.hrl").
-include_lib("../src/log.hrl").

% Parse a string such as "1+2" to return {ok, sets:from_list([1,2])}
-spec parse_versions(string()) -> {ok, sets:set(integer())} | error.
parse_versions(S) ->
    Comps = string:split(S, "+", all),
    try
        {ok, sets:from_list(lists:map(fun list_to_integer/1, Comps))}
    catch error:badarg:_ ->
        error
    end.

% Parse a filename such as "foo_V1+2.erl" to return {ok, "foo.erl", sets:from_list([1,2])}
-spec parse_filename(file:name()) -> {ok, string(), sets:set(integer())} | error.
parse_filename(Name) ->
    case filename:extension(Name) =:= ".erl" of
        false -> error;
        true ->
            Root = filename:rootname(Name),
            case string:split(Root, "_", trailing) of
                [Start, "V" ++ VersionsString] ->
                    case parse_versions(VersionsString) of
                        {ok, Versions} -> {ok, Start ++ ".erl", Versions};
                        error -> error
                    end;
                _ -> error
            end
    end.

% Look in the given directory for files of a certain version. For example, if the directory
% contains "foo_V1.erl" and "bar_V1+2.erl", and the version is 2, then the result is
% [{bar_V1+2.erl", "bar.erl"}]
-spec get_files_with_version(file:name(), integer()) -> [{file:name(), file:name()}].
get_files_with_version(Dir, Version) ->
    Files =
        case file:list_dir(Dir) of
            {ok, X} -> X;
            E -> ?ABORT("Error listing content of ~p: ~p", Dir, E)
        end,
    lists:filtermap(
        fun(Filename) ->
            case parse_filename(Filename) of
                error -> false;
                {ok, Name, Versions} ->
                    case sets:is_element(Version, Versions) of
                        true -> {true, {Filename, Name}};
                        false -> false
                    end
            end
        end,
        Files).

-type tycheck_mode() :: tycheck | dont_tycheck.

-spec run_typechecker(file:name(), tycheck_mode()) -> [file:name()].
run_typechecker(SrcDir, Mode) ->
    Opts = #opts{
        files = [filename:join(SrcDir, "main.erl")],
        project_root = SrcDir,
        mode = test_mode,
        no_type_checking = (Mode =:= dont_tycheck)
    },
    ety_main:doWork(Opts).

-spec test_recompile_version(
    file:name(), file:name(), integer(), string(), [string()] | type_error, tycheck_mode()
) -> ok.
test_recompile_version(TargetDir, Dir, Version, RebarLockContent, ExpectedChanges, Mode) ->
    ?LOG_NOTE("Testing code version ~p in ~p", Version, Dir),
    % cleanup of previous source files
    {ok, ExistingFiles} = file:list_dir(TargetDir),
    lists:foreach(
        fun(F) ->
            case filename:extension(F) =:= ".erl" andalso filelib:is_regular(F) of
                true -> file:delete(F);
                false -> ok
            end
        end, ExistingFiles),
    % Copy new source files
    Files = get_files_with_version(Dir, Version),
    lists:foreach(fun({SrcFile,TargetFile}) ->
            From = filename:join(Dir, SrcFile),
            To = filename:join(TargetDir,TargetFile),
            ?LOG_INFO("Copying ~p to ~p", From, To),
            file:copy(From, To)
        end, Files),
    utils:mkdirs(filename:join(TargetDir, "_build/default/lib")),
    file:write_file(filename:join(TargetDir, "rebar.lock"), RebarLockContent),
    RealChanges =
        try
            run_typechecker(TargetDir, Mode)
        catch throw:{ety, ty_error, _}:_ -> type_error
        end,
    ExpectedChangesSorted =
        if is_list(ExpectedChanges) -> lists:sort(ExpectedChanges);
           true -> ExpectedChanges
        end,
    RealChangesSorted =
        if is_list(RealChanges) -> lists:sort(lists:map(fun filename:basename/1, RealChanges));
           true -> RealChanges
        end,
    ?assertEqual(ExpectedChangesSorted, RealChangesSorted),
    ?LOG_NOTE("Test successful for code version ~p in ~p", Version, Dir).

-type changes_map() :: #{integer() => [string()] | compile_error }.

-spec test_recompile(file:name(), changes_map()) -> ok.
test_recompile(Dir, VersionMap) ->
    test_recompile(Dir, VersionMap, tycheck).

-spec test_recompile_dont_tycheck(file:name(), changes_map()) -> ok.
test_recompile_dont_tycheck(Dir, VersionMap) ->
    test_recompile(Dir, VersionMap, dont_tycheck).

-spec test_recompile(file:name(), changes_map(), tycheck_mode()) -> ok.
test_recompile(Dir, VersionMap, Mode) ->
    Versions = lists:sort(maps:keys(VersionMap)),
    tmp:with_tmp_dir(Dir, "root", delete,
        fun(TargetDir) ->
            lists:foreach(
                fun(V) ->
                    test_recompile_version(TargetDir,
                        filename:join("test_files/recompilation/", Dir),
                        V,
                        "rebar.lock_1",
                        maps:get(V, VersionMap),
                        Mode)
                end, Versions)
        end).

test_rebar_changes() ->
    Dir = "rebar_changes",
    tmp:with_tmp_dir(Dir, "root", delete,
        fun(TargetDir) ->
            test_recompile_version(TargetDir,
                filename:join("test_files/recompilation/", Dir),
                1,
                "rebar.lock_1",
                ["main.erl"],
                tycheck),
            test_recompile_version(TargetDir,
                filename:join("test_files/recompilation/", Dir),
                2,
                "rebar.lock_1",
                [],
                tycheck),
            test_recompile_version(TargetDir,
                filename:join("test_files/recompilation/", Dir),
                3,
                "rebar.lock_2",
                ["main.erl"],
                tycheck)
        end).

file_changes_test_() ->
    [?_test(test_recompile("simple", #{1 => ["main.erl"], 2 => []})),
     ?_test(test_recompile("file_changes",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["foo.erl"]})),
     ?_test(test_recompile("file_changes2",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["foo.erl"]})),
      % FIXME: substitution of tally variables causes a timeout
     ?_test(test_recompile_dont_tycheck("change_tyspec",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["main.erl", "foo.erl"]})),
     ?_test(test_recompile("change_local_tyspec",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["foo.erl"]})),
     ?_test(test_recompile("no_type_error",
        #{1 => ["foo.erl", "main.erl"], 2 => ["foo.erl"], 3 => []})),
     ?_test(test_recompile("type_error",
        #{1 => ["foo.erl", "main.erl"], 2 => type_error, 3 => type_error})),
     % FIXME: the following tests use the _dont_tycheck alternative because of some subtype bug
     ?_test(test_recompile_dont_tycheck("change_tydef",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["main.erl", "foo.erl"]})),
     ?_test(test_recompile_dont_tycheck("change_local_tydef",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["foo.erl"]})),
     ?_test(test_recompile_dont_tycheck("change_local_but_reachable_tydef",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["main.erl", "foo.erl"]})),
     ?_test(test_recompile_dont_tycheck("cycle",
        #{1 => ["m1.erl", "m2.erl", "main.erl"], 2 => ["m1.erl", "m2.erl"]})),
     ?_test(test_rebar_changes())
    ].

