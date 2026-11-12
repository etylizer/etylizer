-module(corrected).
-export([get/1]).

-spec get([atom(), ...]) -> atom().
get(L) -> first(L).

% a wrong result type
-spec first([atom(), ...]) -> integer().
first([X | _]) -> X.
