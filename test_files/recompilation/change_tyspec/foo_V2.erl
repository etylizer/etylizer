-module(foo).

-export([foo_fun/2]).

-spec foo_fun(boolean(), any()) -> boolean().
foo_fun(X, _) -> bar:bar_fun(X).

