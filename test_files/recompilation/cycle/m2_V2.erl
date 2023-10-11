-module m1.

-export([f2/1]).

-spec f2(any()) -> boolean().
f2(X) when is_boolean(X) ->
    if
        X =:= false -> true;
        true -> X or m1:f1(X and true)
    end;
f2(_) -> true.
