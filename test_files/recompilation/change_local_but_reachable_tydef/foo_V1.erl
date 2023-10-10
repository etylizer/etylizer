-module(foo).

-export([foo_fun/2]).
-export_type([foo_type/0]).

-type foo_type() :: local_ty1().
-type local_ty1() :: local_ty2().
-type local_ty2() :: boolean().

-spec foo_fun(boolean(), foo_type()) -> boolean().
foo_fun(X, _) -> bar:bar_fun(X).

