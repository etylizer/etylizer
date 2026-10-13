-module(foo).

-export([f1/0, f2/0]).

-include("log.hrl").

-spec f1() -> integer().
f1() ->
    X = 1,
    X + 1.

-spec f2() -> integer().
f2() ->
    ?LOG_DEBUG("f2"),
    2.
