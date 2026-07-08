-module(indexcalls).
-export([f/4]).
f(X, N, K, M) ->
    _ = element(1, X),
    _ = element(N, X),
    _ = setelement(2, X, v),
    _ = erlang:element(3, X),
    _ = erlang:setelement(K, X, w),
    _ = lists:keyfind(a, 2, X),
    _ = lists:keysort(M, X),
    lists:keystore(a, 3, X, {}).
