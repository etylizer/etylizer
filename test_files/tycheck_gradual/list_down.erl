-module(list_down).

-export([f/1]).

-spec f(list(dynamic())) -> list(integer()).
f(X) -> X.
