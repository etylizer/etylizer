-module(save_div_fail).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-spec save_div(any(), 0) -> none; (integer(), integer()) -> {ok, integer()} .
save_div(X, Y) ->
    case Y of
        0 -> none;
        _ -> {ok, X div Y}
    end.
