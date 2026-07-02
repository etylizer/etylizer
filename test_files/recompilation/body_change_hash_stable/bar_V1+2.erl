-module(bar).

-export([b1/0]).

-spec b1() -> integer().
b1() -> foo:f3().
