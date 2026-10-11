% ERROR
% test_files/tycheck/type_error_msgs/redundant_branch_nested.erl:13:9: Type error: in foo/1, this branch never matches
-module(redundant_branch_nested).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(a) -> 1; (b) -> 2.
foo(X) ->
    case X of
        a -> 1;
        b -> 2;
        c -> Y = {X}, Z = if X =:= c -> 4; true -> 5 end, {Y, Z}
    end.
