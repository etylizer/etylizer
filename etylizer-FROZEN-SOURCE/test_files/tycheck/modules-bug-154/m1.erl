-module(m1).

-compile(export_all).
-compile(nowarn_export_all).

-type blub() :: integer().

-spec foo(blub()) -> integer().
foo(X) -> X.
