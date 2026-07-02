-module(check_if).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-spec bar(integer() | string()) -> boolean().
bar(X) when is_integer(X) -> false;
bar(X) -> length(X) =:= 5.

-spec foo(integer() | string()) -> integer().
foo(X) ->
    B = bar(X),
    if
        is_integer(X) -> X + 1;
        X =:= "foo" -> -1;
        B -> 5;
        true -> 42
    end.

my_test() ->
    ?assertEqual(2, foo(1)),
    ?assertEqual(-1, foo("foo")),
    ?assertEqual(5, foo("huray")),
    ?assertEqual(42, foo("X")).
