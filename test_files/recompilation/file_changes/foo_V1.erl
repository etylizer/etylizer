-module(foo).

-export([foo_fun/2]).

-spec foo_fun(integer(), integer()) -> integer().
foo_fun(X, Y) -> bar:bar_fun(X) + Y.

