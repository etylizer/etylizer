% ERROR
% test_files/tycheck/type_error_msgs/case_result_type.erl:17:13: Type error: expression failed to type check
-module(case_result_type).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(integer()) -> integer().
foo(X) ->
    case X of
        1 -> 2;
        2 ->
            Y = 3,
            Y;
        3 ->
            B = true,
            B;  % type error
        4 -> 5;
        _ -> 42
    end.

