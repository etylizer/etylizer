-module(nonempty_list).

-compile(export_all).
-compile(nowarn_export_all).

-spec id(nonempty_list(integer())) -> nonempty_list(integer()).
id(S) -> S.

-spec foo() -> list(integer()).
foo() -> id([1,2,3]).
