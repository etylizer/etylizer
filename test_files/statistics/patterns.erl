-module(patterns).
-export([f/2, g/1]).
f(X, Y) ->
    case X of
        Z when is_integer(Z) -> Z;
        _ when is_atom(Y) -> Y
    end.
g(A) when is_list(A) -> A;
g(A) -> A.
