-module(constr_solve_tests).

-include_lib("eunit/include/eunit.hrl").

test_search_failing_prefix(I, N) ->
    % io:format("I=~w, N=~w~n", [I, N]),
    L = lists:seq(1, N), % [1,...,N]
    J = constr_solve:search_failing_prefix(L,
        fun(X) -> utils:single(X) end,
        fun(S) -> sets:size(S) =< I end),
    if
        I < 0 -> ?assertEqual(1, J);
        true -> ?assertEqual(I + 1, J)
    end.

search_failing_prefix_simple_test() ->
    Res = constr_solve:search_failing_prefix([1,2,3,4,5],
        fun(X) -> utils:single(X) end,
        fun(S) -> sets:size(S) =< 3 end),
    ?assertEqual(4, Res).

search_failing_prefix_test() ->
    N = 100,
    L = lists:seq(-10, N - 1), % predicate must be false for the whole list.
    lists:foreach(
        fun(I) ->
            test_search_failing_prefix(I, N)
        end,
        L).
