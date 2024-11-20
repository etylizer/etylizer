-module(m2).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar() -> integer().
bar() -> m1:foo(1).
