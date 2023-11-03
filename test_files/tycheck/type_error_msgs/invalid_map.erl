% SKIP (Timeout under rebar, see bug #54)
% ERROR
% test_files/tycheck/type_error_msgs/invalid_map.erl:13:1: Type error: function foo/1 failed to type check against type fun(([integer()]) -> [integer()])
-module(invalid_map).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(atom()) -> integer().
bar(_) -> 0.

-spec foo([integer()]) -> [integer()].
foo(L) -> lists:map(fun bar/1, L).
