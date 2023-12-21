% ERROR
% test_files/tycheck/type_error_msgs/invalid_op.erl:9:1: Type error: function make_foo/1 failed to type check against type fun((string()) -> boolean())
-module(invalid_op).

-compile(export_all).
-compile(nowarn_export_all).

-spec make_foo(string()) -> boolean().
make_foo(S) -> not S.
