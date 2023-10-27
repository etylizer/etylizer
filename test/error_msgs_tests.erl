-module(error_msgs_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("../src/ety_main.hrl").
-include_lib("../src/log.hrl").

-type tycheck_result() :: ok | {fail, string()}.

-spec run_typechecker(file:name()) -> tycheck_result().
run_typechecker(File) ->
    Opts = #opts{
        files = [File],
        project_root = filename:dirname(File),
        mode = test_mode
    },
    try
        ety_main:doWork(Opts),
        ok
    catch
        throw:{ety, ty_error, Msg}:_ -> {fail, Msg};
        throw:{ety, parse_error, Msg}:_ -> {fail, Msg}
    end.

-spec expect_ty_error(file:name(), string()) -> ok.
expect_ty_error(File, Expected) ->
    case run_typechecker(File) of
        ok -> error(utils:sformat("Typechecking ~s did not fail", File));
        {fail, Msg} ->
            case string:find(Msg, Expected) of
                nomatch ->
                    io:format("Error message:~n~s", [Msg]),
                    error(utils:sformat("Error message did not include expected string: ~s", Msg));
                _ -> ok
            end
    end.

file_changes_test_() ->
    [?_test(expect_ty_error("test_files/type_errors/invalid_arg.erl",
        "test_files/type_errors/invalid_arg.erl:11:1: " ++
        "Type error: function make_even/1 failed to type check against type fun((integer()) -> integer())")),
     ?_test(expect_ty_error("test_files/type_errors/invalid_op.erl",
        "test_files/type_errors/invalid_op.erl:7:1: " ++
        "Type error: function make_foo/1 failed to type check against type fun((string()) -> boolean())")),
     ?_test(expect_ty_error("test_files/type_errors/invalid_result.erl",
        "test_files/type_errors/invalid_result.erl:7:1: " ++
        "Type error: function make_even/1 failed to type check against type fun((integer()) -> integer())")),
     ?_test(expect_ty_error("test_files/type_errors/non_exhaustive_case.erl",
        "test_files/type_errors/non_exhaustive_case.erl:8:5: Type error: not all cases are covered")),
     ?_test(expect_ty_error("test_files/type_errors/seq.erl",
        "test_files/type_errors/seq.erl:14:9: Type error: expression failed to type check\n" ++
        "%   14|     X = foo(J), % error here")),
     ?_test(expect_ty_error("test_files/type_errors/syntax_error.erl",
        "Error parsing test_files/type_errors/syntax_error.erl"))
    % missing: redundant_branch.erl (see bug #55)
    % Timeout under rebar (see bug #54)
    % ?_test(expect_ty_error("test_files/type_errors/invalid_map.erl",
    %    "test_files/type_errors/invalid_map.erl:10:1: " ++
    %    "Type error: function foo/1 failed to type check against type fun(([integer()]) -> [integer()])")),
    % ?_test(expect_ty_error("test_files/type_errors/invalid_scrutiny.erl",
    %    "test_files/type_errors/invalid_scrutiny.erl:11:10: Type error: expression failed to type check\n" ++
    %    "%   11|     case bar(X) of\n" ++
    %    "%     |          ^"))
    ].