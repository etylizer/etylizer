-module(bar).

-export([b1/0, b2/0]).

-spec b1() -> boolean().
b1() -> foo:f1().

-spec b2() -> boolean().
b2() -> true.
