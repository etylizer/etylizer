-module(invalid_arg).
% Bug #53

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(boolean()) -> boolean().
bar(X) -> X.

-spec foo(boolean()) -> boolean().
foo(B) ->
    B2 = B,
    case bar(B2) of
        _ -> B2
    end.
