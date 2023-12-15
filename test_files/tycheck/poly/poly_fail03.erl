-module(poly_fail03).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(integer()) -> integer().
foo(X) -> X.

-spec bar(T, T) -> integer().
bar(X, _Y) ->
    case foo(X) of
        _ -> 1
    end.
