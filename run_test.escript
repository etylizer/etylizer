#!/usr/bin/env escript
%% run_test.escript
%% Usage: escript run_test.escript <pattern> [<pattern2>]
%%
%% All patterns must match (AND). Use multiple args to combine filters.
%%
%% Examples:
%%   escript run_test.escript case_01
%%   escript run_test.escript "guards.erl/case_01"
%%   escript run_test.escript "(typecheck)"
%%   escript run_test.escript "(infer)"
%%   escript run_test.escript bin_cons "(typecheck)"

-mode(compile).

main(Patterns) when length(Patterns) >= 1 ->
    compile_project(),
    setup_paths(),
    io:format("Evaluating generator...~n"),
    Tests = tycheck_simple_tests:simple_test_(),
    Filtered = lists:foldl(fun(Pat, Acc) -> filter_tests(Acc, Pat) end, Tests, Patterns),
    case Filtered of
        [] ->
            io:format("No tests matching ~p~n", [Patterns]),
            halt(1);
        _ ->
            io:format("Running ~b test(s) matching ~p~n",
                       [count(Filtered), Patterns]),
            case eunit:test(Filtered, [verbose]) of
                ok -> halt(0);
                _  -> halt(2)
            end
    end;
main(_) ->
    io:format("Usage: escript run_test.escript <pattern> [<pattern2>]~n"),
    halt(1).

compile_project() ->
    io:format("Compiling (rebar3 as test compile)...~n"),
    Port = open_port({spawn, "rebar3 as test compile"}, [stream, exit_status, use_stdio, stderr_to_stdout]),
    compile_wait(Port).

compile_wait(Port) ->
    receive
        {Port, {data, Data}} -> io:put_chars(Data), compile_wait(Port);
        {Port, {exit_status, 0}} -> ok;
        {Port, {exit_status, N}} -> io:format("rebar3 compile failed with exit code ~b~n", [N]), halt(1)
    end.

setup_paths() ->
    Dirs = filelib:wildcard("_build/test/lib/*/ebin")
        ++ filelib:wildcard("_build/test/lib/*/test")
        ++ filelib:wildcard("_build/test/extras/test/ebin"),
    [code:add_pathz(D) || D <- Dirs].

filter_tests(Tests, Pat) when is_list(Tests) ->
    lists:filtermap(fun(T) -> filter_test(T, Pat) end, Tests);
filter_tests(Test, Pat) ->
    case filter_test(Test, Pat) of
        {true, T} -> [T];
        false -> []
    end.

filter_test({timeout, N, T}, Pat) ->
    case filter_test(T, Pat) of
        {true, T1} -> {true, {timeout, N, T1}};
        false -> false
    end;
filter_test({Desc, Fun}, Pat) when is_list(Desc), is_function(Fun, 0) ->
    case string:find(Desc, Pat) of
        nomatch -> false;
        _ -> {true, {Desc, Fun}}
    end;
filter_test({Desc, Tests}, Pat) when is_list(Desc), is_list(Tests) ->
    case filter_tests(Tests, Pat) of
        [] -> false;
        F -> {true, {Desc, F}}
    end;
filter_test(L, Pat) when is_list(L) ->
    case filter_tests(L, Pat) of
        [] -> false;
        F -> {true, F}
    end;
filter_test(_, _) -> false.

count(Tests) when is_list(Tests) -> lists:sum([count(T) || T <- Tests]);
count({timeout, _, T}) -> count(T);
count({_, Fun}) when is_function(Fun, 0) -> 1;
count({_, Tests}) when is_list(Tests) -> count(Tests);
count(_) -> 1.
