-module(poly).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(T) -> T.
bar(X) -> X.

-spec foo(boolean()) -> integer().
foo(B) ->
    case bar(B) of
        true -> bar(1);
        false -> 42
    end.
