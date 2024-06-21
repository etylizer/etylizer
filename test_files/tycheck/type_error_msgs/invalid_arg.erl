% ERROR
% test_files/tycheck/type_error_msgs/invalid_arg.erl:13:17: Type error: expression failed to type check
-module(invalid_arg).

-compile(export_all).
-compile(nowarn_export_all).

-spec make_foo(boolean()) -> integer().
make_foo(true) -> 0;
make_foo(false) -> 1.

-spec make_even(integer()) -> integer().
make_even(X) -> make_foo(X).
