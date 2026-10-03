-module(foo).

-export([broken/0, safe/0]).

-spec broken() -> boolean().
broken() -> 42.

-spec safe() -> boolean().
safe() -> true.
