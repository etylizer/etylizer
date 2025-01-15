% ERROR
% test_files/tycheck/type_error_msgs/seq_last.erl:21:28: Type error: in foo/1, expression failed to type check
-module(seq_last).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(any()) ->  boolean().
bar(X) ->
    case X of
        1 -> true;
        _ -> false
    end.

-spec foo(boolean()) -> boolean().
foo(B) ->
    _B2 = not B,
    I = if B -> 1; true -> 2 end,
    J = bar(I),
    X = foo(J),
    if X -> false; true -> 2 end.
                         % ^ error here
