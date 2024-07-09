% ERROR
% test_files/tycheck/type_error_msgs/invalid_scrutiny3.erl:14:18: Type error: expression failed to type check
-module(invalid_scrutiny3).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(integer()) -> integer().
bar(X) -> X + 1.

-spec foo() -> integer().
foo() ->
    X = 
        case bar(true) of
            1 -> 42;
            _ -> 0
        end,
    X + 1.
