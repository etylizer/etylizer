-module(fun_up).

-export([f/1]).

-spec f(fun((integer()) -> atom())) -> fun((integer()) -> dynamic()).
f(X) -> X.
