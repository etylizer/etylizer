-module(use).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(types:blub()) -> integer().
foo(X) -> X.
