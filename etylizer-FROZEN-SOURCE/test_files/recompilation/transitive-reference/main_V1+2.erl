-module(m1).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo() -> integer().
foo() -> m2:bar(1).
