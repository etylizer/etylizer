-module(foo).

-export([foo_fun/2]).

-spec foo_fun(integer(), any()) -> integer().
foo_fun(X, _) -> bar:bar_fun(X).

