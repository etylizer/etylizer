% ERROR
% test_files/tycheck/type_error_msgs/redundant_branch.erl:13:9: Type error: in foo/1, this branch never matches
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
