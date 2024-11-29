-module(nonempty_string).

-compile(export_all).
-compile(nowarn_export_all).

-spec id(nonempty_string()) -> nonempty_string().
id(S) -> S.

-spec foo() -> string().
foo() -> id("blub").
