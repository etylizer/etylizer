-module(foo).

-export([safe1/0, broken/0]).

-spec safe1() -> boolean().
safe1() -> true.

-spec broken() -> boolean().
broken() -> 42.
