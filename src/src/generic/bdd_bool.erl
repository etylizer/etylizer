-module(bdd_bool).
-vsn({2,0,0}).

% only used as a simple boolean terminal node in a BDD where the leafs are 1 and 0 only.

-behavior(eq).
-export([compare/2, equal/2]).

-behavior(type).
-export([empty/0, any/0]).
-export([union/2, intersect/2, diff/2, negate/1, is_any/1]).
-export([is_empty/1, eval/1]).

compare(0, 0) -> 0; compare(1, 1) -> 0; compare(1, 0) -> 1; compare(0, 1) -> -1.
equal(X, Y) -> X =:= Y.
empty() -> 0.
any() -> 1.
union(X, Y) -> erlang:max(X, Y).
intersect(X, Y) -> erlang:min(X, Y).
diff(_, 1) -> 0; diff(X, _) -> X.
negate(1) -> 0; negate(0) -> 1.
is_any(1) -> true; is_any(_) -> false.
is_empty(0) -> true; is_empty(_) -> false.
eval(_) -> erlang:error(not_implemented).
