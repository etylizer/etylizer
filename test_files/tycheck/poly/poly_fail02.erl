-module(poly_fail02).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(integer()) -> integer().
foo(X) -> X.

-spec bar(T, T) -> integer().
bar(X, _) ->
    case foo(X) of
        Z -> Z
    end.
