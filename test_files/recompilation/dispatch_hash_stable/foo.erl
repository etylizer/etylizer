-module(foo).
-export([f/2, g/0]).

% Multi-clause function: its clauses become a case over generated argument variables.
-spec f(integer(), {a, integer()} | {b, integer()}) -> integer().
f(X, {a, Y}) -> X + Y;
f(X, {b, Y}) -> X - Y.

-spec g() -> integer().
g() -> 42.
