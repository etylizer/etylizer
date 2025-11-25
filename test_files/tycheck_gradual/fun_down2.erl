-module(fun_down2).

-export([f/1]).

-spec f(fun((dynamic()) -> atom())) -> fun((integer()) -> atom()).
f(X) -> X.
