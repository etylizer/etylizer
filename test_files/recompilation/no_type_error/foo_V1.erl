-module(foo).

-export([foo/1]).

-spec foo(integer()) -> integer().
foo(X) -> X.
