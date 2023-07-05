-module(foo).

-export([foo_fun/2]).
-export_type([foo_type/0]).

-type foo_type() :: integer().

-type local_ty() :: integer().

-spec helper(local_ty()) -> integer().
helper(_) -> 1.

-spec foo_fun(integer(), foo_type()) -> integer().
foo_fun(X, Y) -> bar:bar_fun(X) + helper(Y).

