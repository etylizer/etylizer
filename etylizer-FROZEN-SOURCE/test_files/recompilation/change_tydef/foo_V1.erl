-module(foo).

-export([foo_fun/2]).
-export_type([foo_type/0]).

-type foo_type() :: boolean().

-spec foo_fun(boolean(), foo_type()) -> boolean().
foo_fun(X, Y) -> bar:bar_fun(X) and Y.

