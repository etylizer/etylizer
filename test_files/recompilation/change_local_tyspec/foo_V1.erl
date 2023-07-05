-module(foo).

-export([foo_fun/2]).

-spec helper(integer()) -> integer().
helper(X) -> 1 + X.

-spec foo_fun(integer(), integer()) -> integer().
foo_fun(X, Y) -> bar:bar_fun(X) + helper(Y).

