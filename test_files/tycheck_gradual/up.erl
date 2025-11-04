-module(up).

-export([f/1]).

-spec f(integer()) -> dynamic().
f(X) -> X.
