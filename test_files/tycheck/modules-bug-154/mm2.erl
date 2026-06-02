-module(mm2).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar() -> integer().
bar() -> mm1:foo(1).
