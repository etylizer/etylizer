% ERROR
% test_files/tycheck/type_error_msgs/redundant_branch_record.erl:16:9: Type error: in foo/1, this branch never matches
-module(redundant_branch_record).

-compile(export_all).
-compile(nowarn_export_all).

-record(r, {a}).

% the tuple of the record pattern and its tag have the location of the clause
-spec foo(a) -> 1; (b) -> 2.
foo(X) ->
    case X of
        a -> 1;
        b -> 2;
        #r{a = _} -> 3
    end.
