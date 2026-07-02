
-module(module).
-export([foo/2]).

-spec foo(integer(), integer()) -> integer().
foo(X, Y) ->
    2 * X + Y.
