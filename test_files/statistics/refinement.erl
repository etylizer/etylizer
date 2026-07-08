-module(refinement).
-export([r1f/1, r2f/1, r3f/2, r4f/1, none/1]).
r1f(X) -> if X > 0 -> pos; true -> nonpos end.
r2f(Y) -> case a of Y -> m; _ -> n end.
r3f(X, L) -> case L of [_|_] when is_integer(X) -> yes; _ -> no end.
r4f(X) -> Y = X, case foo of Y -> a; _ -> b end.
none(X) -> X + 1.
