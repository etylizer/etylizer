-module(invalid_result).

-compile(export_all).
-compile(nowarn_export_all).

-spec make_even(integer()) -> integer().
make_even(X) ->
    case (X rem 2) == 0 of
        true -> X;
        false -> "foo"
    end.
