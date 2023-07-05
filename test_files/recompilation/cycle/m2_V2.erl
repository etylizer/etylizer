-module m1.

-export([f2/1]).

-spec f2(any()) -> integer().
f2(X) when is_integer(X) ->
    if
        X =:= 0 -> 1;
        true -> X * m1:f1(X-1)
    end;
f2(_) -> 1.
