-module(foo).

-export([f1/0, f2/0]).

-spec f2() -> boolean().
f2() -> false.

-spec f1() -> boolean().
f1() -> f2().
