-module(foo).

-export([broken/0]).

-spec broken() -> boolean().
broken() -> 42.
