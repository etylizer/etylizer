% ERROR
% test_files/tycheck/type_error_msgs/invalid_scrutiny.erl:16:14: Type error: in foo/1, expression failed to type check
% %   16|     case bar(X) of
% %     |              ^
-module(invalid_scrutiny).
% SKIP (Timeout under rebar, see bug #54)

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(integer()) -> a | b |c .
bar(_) -> a.

-spec foo(a | b | c) -> integer().
foo(X) ->
    case bar(X) of
        a -> 1;
        b -> 2;
        c -> 3
    end.
