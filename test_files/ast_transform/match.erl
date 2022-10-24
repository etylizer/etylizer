-module(match).

-compile(export_all).
-compile(nowarn_export_all).

bar(X, {_, Y}) -> X + Y.

foo() ->
    {A, B} = {1, {2,3}},
    E = bar(C = A, {D, _} = B),
    T = {A, B, C, D, E}. % expected result: {1, {2,3}, 1, 2, 4}
