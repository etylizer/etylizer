-module(ast_transform_test).

-export([check/1]).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

% -spec unconsult(file:filename(), term()) -> ok | {error, any()}.
% unconsult(F, T) ->
%     L = if is_list(T) -> T;
%            true -> [T]
%         end,
%     {ok, S} = file:open(F, [write]),
%     lists:foreach(fun(X) -> io:format(S, "~200p.~n", [X]) end, L),
%     file:close(S).

-spec diff_terms(term(), term(), delete | dont_delete) -> equal | {diff, string()}.
diff_terms(T1, T2, _) when T1 == T2 -> equal;
diff_terms(T1, T2, Del) ->
    P = "terms_",
    S = ".erl",
    tmp:with_tmp_file(P ++ "1_", S, Del, fun (F1, P1) ->
        tmp:with_tmp_file(P ++ "2_", S, Del, fun (F2, P2) ->
            io:format(F1, "~200p", [T1]),
            io:format(F2, "~200p", [T2]),
            file:close(F1),
            file:close(F2),
            Out = os:cmd(utils:sformat("diff -u ~s ~s", P1, P2)),
            {diff, Out}
        end)
    end).

-spec check_test_spec(file:filename(), test_utils:test_spec()) -> ok.
check_test_spec(Path, {good, Lineno, RawForms}) ->
    Forms = ast_utils:remove_locs(ast_transform:trans(Path, RawForms)),
    {Spec, Mod} = ast_check:parse_spec("src/ast.erl"),
    Result = ast_check:check_against_type(Spec, Mod, forms, Forms),
    case Result of
        true -> ok;
        _ ->
            io:format("Test in ~s:~w failed: "
                      "Checking the result of the transforamtion against type ~w:form "
                      "returned ~w instead of true",
                      [Path, Lineno, Mod, Result]),
            ?assert(false)
    end,
    OutPath = filename:rootname(Path) ++ ".out",
    % unconsult(OutPath, [Forms]), % DANGER, this line should be commented out
    ?LOG_NOTE("Loading expected forms from ~s", OutPath),
    {ok, [Expected]} = file:consult(OutPath),
    ?LOG_NOTE("Found expected forms in ~s", OutPath),
    case diff_terms(Expected, Forms, dont_delete) of
        equal -> ok;
        {diff, S} ->
            io:format("Test in ~s:~w failed: "
                "AST does not have the right form after transformation. "
                "Diff (--- expected, +++ given):~n~s", [Path, Lineno, S]),
            ?assert(false)
    end;
check_test_spec(Path, {{bad, SearchPattern}, Lineno, RawForms}) ->
    try ast_transform:trans(Path, RawForms),
        io:format("Test in ~s:~w should fail but did not", [Path, Lineno]),
        ?assert(false)
    catch throw:{etylizer, _, Msg} ->
        case string:find(Msg, SearchPattern) of
            nomatch ->
                io:format("Test in ~s:~w failed as expected, but with an unexpected "
                    "error message: ~s (expected ~s)", [Path, Lineno, Msg, SearchPattern]),
                ?assert(false);
            _ -> ok
        end
    end.

-spec check(file:filename()) -> ok.
check(Path) ->
    Tests = test_utils:extract_tests(Path),
    lists:foreach(fun (T) -> check_test_spec(Path, T) end, Tests).

all_file_test_() ->
    TestFiles = filelib:wildcard("test_files/ast_transform/*.erl"),
    lists:map(fun(P) -> {P, fun() -> check(P) end} end, TestFiles).
