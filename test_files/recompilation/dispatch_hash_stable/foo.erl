-module(foo).
-export([f/2, g/0]).

% Multi-clause function with arity >= 2, one direct position and one complex position.
% This triggers ast_transform:rewrite_dispatched_clauses which generates $dispatch variables.
-spec f(integer(), {a, integer()} | {b, integer()}) -> integer().
f(X, {a, Y}) -> X + Y;
f(X, {b, Y}) -> X - Y.

-spec g() -> integer().
g() -> 42.
