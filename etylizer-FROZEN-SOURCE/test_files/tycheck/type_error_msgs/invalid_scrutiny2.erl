% ERROR
% test_files/tycheck/type_error_msgs/invalid_scrutiny2.erl:16:18: Type error: in foo/0, expression failed to type check
-module(invalid_scrutiny2).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(integer()) -> integer().
bar(X) -> X + 1.

-spec foo() -> integer().
foo() ->
    X = 
        case bar(1) of
            1 -> 42;
            Y -> Y + true
        end,
    X + 1.
