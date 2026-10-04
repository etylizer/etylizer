-module(scope_fun_3).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars, nowarn_unused_vars]).

% Sizes and map keys in a fun head refer to the scope around the fun,
% sizes also to the segments before them.
foo(N, K, L) ->
    F1 = fun(<<X:N, _/bitstring>>) -> X end,
    F2 = fun(N, <<X:N, _/bitstring>>) -> X end,
    F3 = fun(<<N:8, X:N, _/bitstring>>) -> X end,
    F4 = fun(#{K := V}) -> V end,
    F5 = fun(K, #{K := V}) -> V end,
    L1 = [X || {N, <<X:N, _/bitstring>>} <- L],
    {F1, F2, F3, F4, F5, L1}.
