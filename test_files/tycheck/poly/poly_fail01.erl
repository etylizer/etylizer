-module(poly_fail_01).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(integer()) -> integer().
foo(X) -> X.

-spec bar(T, T) -> integer().
bar(X, _Y) -> foo(X).
