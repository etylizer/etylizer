-module m1.

-export([f2/1]).

-spec f2(integer()) -> integer().
f2(X) ->
    if
        X =:= 0 -> 1;
        true -> X * m1:f1(X-1)
    end.
