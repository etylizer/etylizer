-module(typecase).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-spec foo_infer(integer() | string()) -> integer() | string().
foo_infer(X) when is_integer(X) -> X + 1;
foo_infer(X) -> X ++ "_abc".

-spec foo2_infer(integer() | string()) -> integer() | string().
foo2_infer(X) when is_integer(X) -> "foo";
foo2_infer(X) -> string:length(X).

-spec foo(integer()) -> integer(); (string()) -> string().
foo(X) when is_integer(X) -> X + 1;
foo(X) -> X ++ "_abc".

my_test() ->
    ?assertEqual(2, foo_infer(1)),
    ?assertEqual("foo_abc", foo_infer("foo")),
    ?assertEqual(2, foo(1)),
    ?assertEqual("foo_abc", foo("foo")),
    ?assertEqual("foo", foo2_infer(1)),
    ?assertEqual(3, foo2_infer("foo")).
