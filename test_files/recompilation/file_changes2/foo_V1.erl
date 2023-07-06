-module(foo).

-export([foo_fun/2]).
-import(bar, [bar_fun/1]).

-spec foo_fun(integer(), integer()) -> integer().
foo_fun(X, Y) -> bar_fun(X) + Y.
