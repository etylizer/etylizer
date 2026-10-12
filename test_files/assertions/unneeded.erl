-module(unneeded).
-export([first/1]).

-spec first([integer(), ...]) -> integer().
first(L) ->
    [X | _] = L,
    X.
