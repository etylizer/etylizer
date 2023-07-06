-module m1.

-export([f1/1]).

-spec f1(integer()) -> integer().
f1(X) -> m2:f2(X).
