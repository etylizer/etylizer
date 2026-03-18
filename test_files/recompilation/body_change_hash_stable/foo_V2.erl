-module(foo).

-export([f1/0, f2/0, f3/0]).

-spec f1() -> integer().
f1() ->
    X = 1,
    X + 1.

-spec f2() -> integer().
f2() -> 2.

-spec f3() -> integer().
f3() -> 3.
