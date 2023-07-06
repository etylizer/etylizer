-module(foo).

-export([foo_fun/2]).
-export_type([foo_type/0]).

-type foo_type() :: integer().

-spec foo_fun(integer(), foo_type()) -> integer().
foo_fun(X, Y) -> bar:bar_fun(X) + Y.

