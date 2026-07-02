-module(module4).

-export([add/2]).

-spec add(integer(), integer()) -> integer().
add(X, Y) ->
    X + Y.
