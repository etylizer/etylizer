-module(concat).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(string()) -> string().
foo(S) -> S ++ "X".
