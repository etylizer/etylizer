-module(bar).

-export([b1/0, b2/0, b3/0]).

-spec b1() -> boolean().
b1() -> foo:f1().

% the call is nested in another call
-spec b2() -> boolean().
b2() -> id(foo:f1()).

-spec b3() -> boolean().
b3() -> true.

-spec id(T) -> T.
id(X) -> X.
