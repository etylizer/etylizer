-module(foo).

-export([safe1/0, safe2/0, broken/0]).

-spec safe1() -> boolean().
safe1() -> true.

-spec safe2() -> integer().
safe2() -> 42.

-spec broken() -> boolean().
broken() -> false.
