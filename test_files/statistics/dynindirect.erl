-module(dynindirect).
-export([f/0, g/0, h/0]).
-type dyn() :: dynamic().
-type wrap() :: {atom(), dyn()}.
-type plain() :: integer().
-spec f() -> dyn().
f() -> foo.
-spec g() -> wrap().
g() -> {a, b}.
-spec h() -> plain().
h() -> 1.
