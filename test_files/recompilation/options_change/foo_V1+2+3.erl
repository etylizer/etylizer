-module(foo).

-export([foo_fun/0]).

-spec foo_fun() -> integer().
foo_fun() -> 2.
