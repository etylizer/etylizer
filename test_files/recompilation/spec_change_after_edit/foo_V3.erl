-module(foo).

-export([f1/0, f2/0]).

-spec f1() -> boolean() | integer().
f1() -> true.

-spec f2() -> integer().
f2() -> 2.
