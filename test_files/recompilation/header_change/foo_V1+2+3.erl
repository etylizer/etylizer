-module(foo).

-export([f/1, g/0]).

-include("foo.hrl").

-spec f(t()) -> t().
f(X) -> X.

-spec g() -> integer().
g() -> ?VAL.
