-module m1.

-export([f1/1]).

-spec f1(boolean()) -> boolean().
f1(X) -> m2:f2(X).
