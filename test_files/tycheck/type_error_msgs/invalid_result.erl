% ERROR
% test_files/tycheck/type_error_msgs/invalid_result.erl:12:18: Type error: in make_even/1, expression failed to type check
-module(invalid_result).

-compile(export_all).
-compile(nowarn_export_all).

-spec make_even(integer()) -> integer().
make_even(X) ->
    case (X rem 2) == 0 of
        true -> X;
        false -> "foo"
    end.
