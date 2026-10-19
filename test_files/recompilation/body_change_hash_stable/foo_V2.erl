-module(foo).

-export([f1/0, f2/0, f3/0, f4/2]).

-spec f1() -> integer().
f1() ->
    X = 1,
    X + 1.

-spec f2() -> integer().
f2() -> 2.

-spec f3() -> integer().
f3() -> 3.

% Its clauses become a case over generated argument variables.
-spec f4(integer(), {a, integer()} | {b, integer()}) -> integer().
f4(X, {a, Y}) -> X + Y;
f4(X, {b, Y}) -> X - Y.
