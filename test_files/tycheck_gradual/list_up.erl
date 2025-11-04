-module(list_up).

-export([f/1]).

-spec f(list(integer())) -> list(dynamic()).
f(X) -> X.
