% ERROR
% test_files/tycheck/type_error_msgs/invalid_op.erl:9:16: Type error: expression failed to type check
-module(invalid_op).

-compile(export_all).
-compile(nowarn_export_all).

-spec make_foo(string()) -> boolean().
make_foo(S) -> not S.
