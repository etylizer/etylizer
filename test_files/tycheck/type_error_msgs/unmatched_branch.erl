% ERROR
% test_files/tycheck/type_error_msgs/unmatched_branch.erl:11:9: Type error: this branch never matches
-module(unmatched_branch).

-compile(export_all).
-compile(nowarn_export_all).

-spec unmatched(integer()) -> integer().
unmatched(X) ->
    case X of
        none -> 0
    end.
