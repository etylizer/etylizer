-module(recursive).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

foo(0, _) -> [];
foo(N, X) -> bar(N, X).

bar(0, _) -> [];
bar(N, X) -> [X | foo(N - 1, X)].

-spec spam() -> list(string() | integer()).
spam() ->
    bar(4, "string") ++ bar(2, 42).

my_test() ->
    ?assertEqual(["string", "string", "string", "string", 42, 42], spam()).
