-module(invalid_op).

-compile(export_all).
-compile(nowarn_export_all).

-spec make_foo(string()) -> boolean().
make_foo(S) -> not S.
