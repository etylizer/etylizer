
-module(module).
-export([foo/1]).

-spec foo(integer()) -> integer().
foo(X) ->
    2 * X.
