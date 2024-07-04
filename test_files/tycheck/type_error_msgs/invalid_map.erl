% ERROR
% test_files/tycheck/type_error_msgs/invalid_map.erl:12:32: Type error: expression failed to type check
-module(invalid_map).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(atom()) -> integer().
bar(_) -> 0.

-spec foo([integer()]) -> [integer()].
foo(L) -> lists:map(fun bar/1, L).
