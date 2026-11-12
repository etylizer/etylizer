-module(overlaid).
-export([first/1]).

-spec first([atom(), ...]) -> atom().
first([X | _]) -> X.
