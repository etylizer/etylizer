-module(redundant_branch).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(a | b | c) -> integer().
foo(X) ->
    case X of
        a -> 1;
        c -> 3
    end.
