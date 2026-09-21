-module(foo).

-export([f1/0]).

-spec f1() -> boolean() | integer().
f1() -> true.
