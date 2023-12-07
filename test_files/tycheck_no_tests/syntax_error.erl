% ERROR
% Error parsing
-module(test).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(boolean()) -> integer().
foo(B) ->
    I = if B andalso not B -> 1; true -> 2.
    I.
