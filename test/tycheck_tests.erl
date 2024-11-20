-module(tycheck_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("../src/ety_main.hrl").
-include_lib("../src/log.hrl").

-type tycheck_result() :: ok | {fail, string()}.

-spec run_typechecker(file:name()) -> tycheck_result().
run_typechecker(File) ->
    Opts = #opts{
        files = [File],
        project_root = filename:dirname(File),
        mode = test_mode,
        force = true
    },
    try
        ety_main:doWork(Opts),
        ok
    catch
        throw:{ety, ty_error, Msg}:_ -> {fail, Msg};
        throw:{ety, parse_error, Msg}:_ -> {fail, Msg}
    end.

-type error_msg() :: unspecific | string().

-spec run_failing_test(file:name(), error_msg()) -> ok.
run_failing_test(File, ExpectedErrMsg) ->
    case run_typechecker(File) of
        ok -> error(utils:sformat("Typechecking ~s did not fail", File));
        {fail, Msg} ->
            case ExpectedErrMsg of
                unspecific -> ok;
                _ ->
                    case string:find(Msg, ExpectedErrMsg) of
                        nomatch ->
                            ?LOG_NOTE("Error message:~n~s", Msg),
                            error(utils:sformat("Error message did not include expected string:~n" ++
                                "Expected: ~s~nGiven   : ~s", ExpectedErrMsg, Msg));
                        _ ->
                            ?LOG_NOTE("Test ~s failed as expected with the right error message", File)
                    end
            end
    end.

-spec run_ok_test(file:name()) -> ok.
run_ok_test(File) ->
    case run_typechecker(File) of
        ok ->
            ?LOG_NOTE("Test ~s typecheck as expected", File),
            ok;
        {fail, Msg} ->
            error(utils:sformat("Typechecking ~s unexpectedly failed with error message:~n~s", File, Msg))
    end.

-spec analyze_test_file(file:name()) -> ok_test | {fail_test, error_msg()} | skip_test.
analyze_test_file(File) ->
    {ok, Regex} = re:compile("_fail\\d*\.erl"),
    IsFail = case re:run(File, Regex) of
        {match, _} -> true;
        nomatch -> false
    end,
    {ok, Lines} = utils:file_get_lines(File),
    CommentLines =
        lists:map(
            fun(S) ->
                case string:trim(S, trailing) of
                    "% " ++ Rest -> Rest;
                    "%" ++ Rest -> Rest
                end
            end,
            lists:takewhile(fun(S) -> string:prefix(S, "%") =/= nomatch end, Lines)
        ),
    ExpectedErrMsg =
        case CommentLines of
            ["ERROR" | Rest] -> string:join(Rest, "\n");
            ["ERROR " ++ _ | Rest] -> string:join(Rest, "\n");
            _ -> unspecific
        end,
    IsSkip =
        case CommentLines of
            ["SKIP" | _] -> true;
            ["SKIP " ++ _ | _] -> true;
            _ -> false
        end,
    ?LOG_DEBUG("IsFail=~p, CommentLines=~p, ExpectedErrMsg=~p, IsSkip=~p",
               IsFail, CommentLines, ExpectedErrMsg, IsSkip),
    case {IsSkip, IsFail, ExpectedErrMsg} of
        {true, _, _} -> skip_test;
        {false, false, unspecific} -> ok_test;
        {false, false, Err} -> {fail_test, Err};
        {false, true, Err} -> {fail_test, Err}
    end.

tycheck_test_() ->
    Files1 = filelib:wildcard("test_files/tycheck/**/*.erl"),
    Files2 = filelib:wildcard("test_files/tycheck_no_tests/**/*.erl"),
    Files = Files1 ++ Files2,
    case Files of
        [] -> error("No test files found");
        _ -> ok
    end,
    lists:flatmap(
        fun(File) ->
            case analyze_test_file(File) of
                skip_test ->
                    ?LOG_NOTE("Skipping test ~s", File),
                    [];
                ok_test ->
                    [
                        {"tycheck_ok " ++ File,
                         fun() ->
                            ?LOG_NOTE("Checking that ~s typechecks successfully", File),
                            run_ok_test(File)
                         end}
                    ];
                {fail_test, Err} ->
                    [
                        {"tycheck_fail " ++ File,
                         fun() ->
                             ?LOG_NOTE("Checking that ~s fails typechecking", File),
                             run_failing_test(File, Err)
                         end}
                    ]
            end
        end, Files).
