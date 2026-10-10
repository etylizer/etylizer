% ERROR
% test_files/tycheck/type_error_msgs/non_exhaustive_fun.erl:9:14: Type error: in foo/0, not all cases are covered
-module(non_exhaustive_fun).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo() -> fun((a | b) -> integer()).
foo() -> fun (a) -> 1 end.
