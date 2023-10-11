-module(foo).

-export([foo_fun/2]).

-spec foo_fun(boolean(), boolean()) -> boolean().
foo_fun(X, Y) -> bar:bar_fun(X) or Y.

