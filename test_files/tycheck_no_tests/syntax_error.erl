% ERROR
% Error parsing test_files/tycheck/type_error_msgs/syntax_error.erl
-module(test).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(boolean()) -> integer().
foo(B) ->
    I = if B andalso not B -> 1; true -> 2.
    I.
