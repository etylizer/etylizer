% ERROR
% test_files/tycheck/type_error_msgs/unmatched_branch.erl:10:5: Type error: in unmatched/1, not all cases are covered
-module(unmatched_branch).

-compile(export_all).
-compile(nowarn_export_all).

-spec unmatched(integer()) -> integer().
unmatched(X) ->
    case X of
        none -> 0
    end.
