-module(redundant_branch).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(a | b) -> integer().
foo(X) ->
    case X of
        a -> 1;
        b -> 2;
        c -> 3
    end.
