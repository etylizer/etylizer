-module(invalid_arg).
% Bug #53

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(boolean()) -> integer().
foo(B) ->
    B2 = not B,
    I = if B andalso B2 -> 1; true -> 2 end,
    I.
