-module(foo).

-export([foo_fun/2]).
-export_type([foo_type/0]).

-type foo_type() :: any().

-spec foo_fun(boolean(), foo_type()) -> boolean().
foo_fun(X, _Y) -> bar:bar_fun(X).

