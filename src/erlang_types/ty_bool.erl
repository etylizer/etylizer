-module(ty_bool).

% only used as a simple boolean terminal node in a BDD where the leafs are 1 and 0 only.
-compile([export_all, nowarn_export_all]).
-export_type([type/0]).

-type type() :: 0 | 1.

compare(0, 0) -> 0; compare(1, 1) -> 0; compare(1, 0) -> 1; compare(0, 1) -> -1.
equal(X, Y) -> X =:= Y.
empty() -> 0.
any() -> 1.
union(X, Y) -> erlang:max(X, Y).
intersect(X, Y) -> erlang:min(X, Y).
difference(_, 1) -> 0; difference(X, _) -> X.
negate(1) -> 0; negate(0) -> 1.
is_any(1) -> true; is_any(_) -> false.
is_empty(0, S) -> {true, S}; is_empty(_, S) -> {false, S}.
substitute(_,X,_,_) -> X.
% there is nothing to substitute in a ty_bool
map_pi(_) -> #{}.
has_ref(_,_) -> false.
all_variables(_, _) -> [].
unparse(0, C) -> {{predef, none}, C};
unparse(1, C) -> {{predef, any}, C}.
