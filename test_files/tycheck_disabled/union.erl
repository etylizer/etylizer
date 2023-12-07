-module(union).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-type success() :: {true, integer()}.
-type error() :: {false, string()}.
-type response() :: success() | error().

get_value({true, X}) -> X.

-spec handle_response_infer(response()) -> integer().
handle_response_infer(R) ->
    case R of
        {true, _} -> get_value(R);
        {false, _} -> -1
    end.

my_test() ->
    ?assertEqual(42, handle_response_infer({true, 42})).
    %?assertEqual(42, handle_response_infer({false, "foo"})).

