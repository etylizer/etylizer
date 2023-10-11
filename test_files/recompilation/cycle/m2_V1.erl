-module m1.

-export([f2/1]).

-spec f2(boolean()) -> boolean().
f2(X) ->
    if
        X =:= 0 -> true;
        true -> X * m1:f1(X-true)
    end.
