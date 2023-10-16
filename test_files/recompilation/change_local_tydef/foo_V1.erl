-module(foo).

-export([foo_fun/2]).
-export_type([foo_type/0]).

-type foo_type() :: boolean().

-type local_ty() :: boolean().

-spec helper(local_ty()) -> boolean().
helper(_) -> true.

-spec foo_fun(boolean(), foo_type()) -> boolean().
foo_fun(X, Y) -> bar:bar_fun(X) and helper(Y).

