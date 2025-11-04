-module(fun_down).

-export([f/1]).

-spec f(fun((integer()) -> dynamic())) -> fun((integer()) -> atom()).
f(X) -> X.
