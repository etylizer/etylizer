-module(bdd_bool).

% only used as a simple boolean terminal node in a BDD where the leafs are 1 and 0 only.

-export([compare/2, equal/2]).

-export([empty/0, any/0]).
-export([union/2, intersect/2, diff/2, negate/1, is_any/1]).
-export([is_empty/1, substitute/4, map_pi/1, has_ref/2, all_variables/2, transform/2, raw_transform/2]).

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
substitute(_,X,_,_) -> X.
% there is nothing to substitute in a bdd_bool
map_pi(_) -> #{}.
has_ref(_,_) -> false.
all_variables(_, _) -> [].
raw_transform(T, Op) -> transform(T, Op).
transform(0, #{empty := E}) -> E();
transform(1, #{any := A}) -> A().
