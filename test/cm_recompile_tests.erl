-module(cm_recompile_tests).

-include_lib("eunit/include/eunit.hrl").
-include("etylizer_main.hrl").
-include("log.hrl").

-define(_timeout(E), {timeout, 45, E}).

% Parse a string such as "1+2" to return {ok, sets:from_list([1,2])}
-spec parse_versions(string()) -> {ok, sets:set(integer())} | error.
parse_versions(S) ->
    Comps = string:split(S, "+", all),
    try
        {ok, sets:from_list(lists:map(fun list_to_integer/1, Comps), [{version, 2}])}
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

-type tycheck_mode() :: tycheck | dont_tycheck | report.

-spec run_typechecker(file:name(), tycheck_mode()) -> cm_check:check_list().
run_typechecker(SrcDir, Mode) ->
    Opts = #opts{
        files = [filename:join(SrcDir, "main.erl")],
        project_root = SrcDir,
        mode = test_mode,
        no_type_checking = (Mode =:= dont_tycheck),
        report_mode = case Mode of report -> report; _ -> early_exit end
    },
    etylizer_main:doWork(Opts).

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
            CheckList = run_typechecker(TargetDir, Mode),
            [F || {F, _} <- CheckList]
        catch throw:{etylizer, ty_error, _}:_ -> type_error
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

-type changes_map() :: #{integer() => [string()] | type_error }.

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

% @doc Normalize a check_list to {BaseName, FunFilter} pairs for comparison.
-spec normalize_check_list(cm_check:check_list()) -> [{string(), all | [{atom(), arity()}]}].
normalize_check_list(CheckList) ->
    Normalized = [{filename:basename(F), Funs} || {F, Funs} <- CheckList],
    lists:sort(Normalized).

% @doc Compare a detailed expected result against the actual check list.
% Expected is either type_error, a list of filenames (file-level), or
% a list of {filename, all | [{atom(), arity()}]} tuples (function-level).
-type detailed_expected() :: type_error | [{string(), all | [{atom(), arity()}]}].
-type detailed_changes_map() :: #{integer() => detailed_expected()}.

-spec test_recompile_version_detailed(
    file:name(), file:name(), integer(), string(), detailed_expected(), tycheck_mode()
) -> ok.
test_recompile_version_detailed(TargetDir, Dir, Version, RebarLockContent, ExpectedChanges, Mode) ->
    ?LOG_NOTE("Testing code version ~p in ~p (detailed)", Version, Dir),
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
        catch throw:{etylizer, ty_error, _}:_ -> type_error
        end,
    case {ExpectedChanges, RealChanges} of
        {type_error, type_error} -> ok;
        {type_error, _} ->
            erlang:error({expected_type_error, got, RealChanges});
        {_, type_error} ->
            erlang:error({expected_check_list, got, type_error});
        _ ->
            RealNormalized = normalize_check_list(RealChanges),
            ExpectedSorted = lists:sort(
                [{F, sort_fun_filter(Funs)} || {F, Funs} <- ExpectedChanges]),
            RealSorted = [{F, sort_fun_filter(Funs)} || {F, Funs} <- RealNormalized],
            ?assertEqual(ExpectedSorted, RealSorted)
    end,
    ?LOG_NOTE("Test successful for code version ~p in ~p (detailed)", Version, Dir).

% @doc Sort function filter for deterministic comparison.
-spec sort_fun_filter(all | [{atom(), arity()}]) -> all | [{atom(), arity()}].
sort_fun_filter(all) -> all;
sort_fun_filter(Funs) -> lists:sort(Funs).

-spec test_recompile_detailed(file:name(), detailed_changes_map(), tycheck_mode()) -> ok.
test_recompile_detailed(Dir, VersionMap, Mode) ->
    Versions = lists:sort(maps:keys(VersionMap)),
    tmp:with_tmp_dir(Dir, "root", delete,
        fun(TargetDir) ->
            lists:foreach(
                fun(V) ->
                    test_recompile_version_detailed(TargetDir,
                        filename:join("test_files/recompilation/", Dir),
                        V,
                        "rebar.lock_1",
                        maps:get(V, VersionMap),
                        Mode)
                end, Versions)
        end).

file_changes_test_() ->
    [
     ?_timeout(?_test(test_recompile("simple", #{1 => ["main.erl"], 2 => []}))),
     ?_timeout(?_test(test_recompile("file_changes",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["foo.erl"]}))),
     ?_timeout(?_test(test_recompile("file_changes2",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["foo.erl"]}))),
      % FIXME: substitution of tally variables causes a timeout
     ?_timeout(?_test(test_recompile_dont_tycheck("change_tyspec",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["main.erl", "foo.erl"]}))),
     ?_timeout(?_test(test_recompile("change_local_tyspec",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["foo.erl"]}))),
     ?_timeout(?_test(test_recompile("no_type_error",
        #{1 => ["foo.erl", "main.erl"], 2 => ["foo.erl"], 3 => []}))),
     ?_timeout(?_test(test_recompile("type_error",
        #{1 => ["foo.erl", "main.erl"], 2 => type_error, 3 => type_error}))),
      % FIXME: the following tests use the _dont_tycheck alternative because of some subtype bug
     ?_timeout(?_test(test_recompile_dont_tycheck("change_tydef",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["main.erl", "foo.erl"]}))),
     ?_timeout(?_test(test_recompile_dont_tycheck("change_local_tydef",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["foo.erl"]}))),
     ?_timeout(?_test(test_recompile_dont_tycheck("change_local_but_reachable_tydef",
        #{1 => ["bar.erl", "foo.erl", "main.erl"], 2 => ["main.erl", "foo.erl"]}))),
     ?_timeout(?_test(test_recompile_dont_tycheck("cycle",
        #{1 => ["m1.erl", "m2.erl", "main.erl"], 2 => ["m1.erl", "m2.erl"]}))),
     ?_timeout(?_test(test_recompile("transitive-reference",
        #{1 => ["main.erl", "m2.erl", "m3.erl", "m4.erl"],
          2 => ["main.erl", "m2.erl", "m3.erl", "m4.erl"]}))),
     ?_timeout(?_test(test_rebar_changes()))
    ].

% @doc Test function-level incremental rechecking after fixing a type error.
% Module foo has 3 functions: safe1, safe2, broken. V1: all OK. V2: broken has type error.
% V3: broken fixed. Only broken/0 should be rechecked in V3.
fun_level_fix_then_recheck_test_() ->
    [?_timeout(?_test(test_recompile_detailed("fix_then_recheck", #{
        1 => [{"foo.erl", all}, {"main.erl", all}],
        2 => type_error,
        3 => [{"foo.erl", [{broken, 0}]}]
    }, tycheck)))].

% @doc Test that changing only a function body does not trigger rechecking of dependents.
% foo has f1 (calls f2) and f2. bar has b1 (calls foo:f1). Changing f2's body (not spec)
% should only recheck f2, not f1 or b1.
fun_level_body_change_test_() ->
    [?_timeout(?_test(test_recompile_detailed("body_change_no_recheck", #{
        1 => [{"bar.erl", all}, {"foo.erl", all}, {"main.erl", all}],
        2 => [{"foo.erl", [{f2, 0}]}]
    }, tycheck)))].

% @doc Test that changing a function's spec triggers rechecking of its dependents.
% foo has f1. bar has b1 (calls foo:f1) and b2 (independent). Changing f1's spec
% should recheck f1 and b1, but not b2 or main.
fun_level_spec_change_test_() ->
    [?_timeout(?_test(test_recompile_detailed("spec_change_recheck", #{
        1 => [{"bar.erl", all}, {"foo.erl", all}, {"main.erl", all}],
        2 => [{"foo.erl", [{f1, 0}]}, {"bar.erl", [{b1, 0}]}]
    }, dont_tycheck)))].

% @doc Test that a persistent type error is still detected on re-run.
% foo has broken/0 which returns integer() instead of boolean(). Both runs
% should produce a type error (the index is not saved after a type error,
% so the second run rechecks everything and still fails).
persistent_type_error_test_() ->
    [?_timeout(?_test(test_recompile("persistent_type_error",
        #{1 => type_error, 2 => type_error})))].

% @doc Test that a failed function does not cause false caller propagation.
% foo:broken/0 has a type error (report mode). On re-run, broken/0 is retried
% but its spec_hash is unchanged, so bar:b1/0 (its caller) is NOT rechecked.
failed_no_caller_recheck_test_() ->
    [?_timeout(?_test(test_recompile_detailed("failed_no_caller_recheck", #{
        1 => [{"bar.erl", all}, {"foo.erl", all}, {"main.erl", all}],
        2 => [{"foo.erl", [{broken, 0}]}]
    }, report)))].

% @doc Test that modifying one function's body (adding lines) does not cause
% other functions in the same file to be rechecked due to unstable hashes.
% foo has f1, f2, f3. V2 changes only f1's body (adds lines, shifting f2/f3 line numbers).
% Only f1/0 should be rechecked - f2, f3, and cross-module caller bar:b1 should not.
body_change_hash_stable_test_() ->
    [?_timeout(?_test(test_recompile_detailed("body_change_hash_stable", #{
        1 => [{"bar.erl", all}, {"foo.erl", all}, {"main.erl", all}],
        2 => [{"foo.erl", [{f1, 0}]}]
    }, tycheck)))].

% @doc Test that report mode re-detects type errors on re-run.
% In report mode, type errors don't throw - the index is saved. Without the fix,
% the second run would find nothing to check (empty check list). With the fix,
% the failed function is excluded from the index and re-checked on the next run.
report_mode_redetect_test_() ->
    [?_timeout(?_test(test_recompile_detailed("report_mode_redetect", #{
        1 => [{"foo.erl", all}, {"main.erl", all}],
        2 => [{"foo.erl", [{broken, 0}]}]
    }, report)))].
