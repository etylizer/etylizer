% ERROR
% test_files/tycheck/type_error_msgs/invalid_arg_in_branch.erl:16:20: Type error: in foo/1, expression failed to type check
-module(invalid_arg_in_branch).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(integer(), integer()) -> integer().
bar(X, Y) -> X + Y.

-spec foo(integer()) -> integer().
foo(X) ->
    case X of
        1 ->
            Y = bar(X, 1),
            bar(Y, foo); % error here, at the second argument
        _ -> 2
    end.
