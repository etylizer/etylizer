-module(save_div).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-spec save_div(any(), 0) -> none; (integer(), neg_integer() | pos_integer()) -> {ok, integer()} .
save_div(X, Y) ->
    case Y of
        0 -> none;
        _ -> {ok, X div Y}
    end.

my_test() ->
    ?assertEqual({ok, 2}, save_div(4,2)),
    ?assertEqual(none, save_div(4,0)).
