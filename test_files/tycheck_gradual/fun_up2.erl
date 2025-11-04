-module(fun_up2).

-export([f/1]).

-spec f(fun((integer()) -> atom())) -> fun((dynamic()) -> atom()).
f(X) -> X.
