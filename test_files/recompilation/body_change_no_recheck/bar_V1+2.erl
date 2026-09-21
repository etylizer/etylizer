-module(bar).

-export([b1/0]).

-spec b1() -> boolean().
b1() -> foo:f1().
