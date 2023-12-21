% ERROR
% test_files/tycheck/type_error_msgs/seq.erl:17:9: Type error: expression failed to type check
% %   17|     X = foo(J), % error here
-module(seq).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(any()) ->  integer().
bar(_) -> 3.

-spec foo(boolean()) -> integer().
foo(B) ->
    _B2 = not B,
    I = if B -> 1; true -> 2 end,
    J = bar(I) + 1,
    X = foo(J), % error here
    X + 1.
