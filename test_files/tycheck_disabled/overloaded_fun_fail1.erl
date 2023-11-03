-module(overloaded_fun_fail1).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(integer()) -> integer();
          (1|2) -> (1|2).
foo(X) ->
    % By swapping the cases, the intersection type above is no longer derivable.
    case X of
        Y -> Y + 1;
        1 -> 2;
        2 -> 1
    end.
