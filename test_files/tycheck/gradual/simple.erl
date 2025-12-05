-module(simple).

-export([main/1]).

-spec f(integer()) -> dynamic().
f(X) -> X + 1.

-spec g(dynamic()) -> dynamic().
g(X) -> X + 1.

% inferred type: integer() -> dynamic()
-spec h(integer()) -> dynamic().
h(X) -> g(f(X)).

-spec main(integer()) -> integer().
main(X) -> h(X).
