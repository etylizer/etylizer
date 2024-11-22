-module(attr_test).

-include_lib("eunit/include/eunit.hrl").


-spec parse_ety_attr_test() -> ok.
parse_ety_attr_test() ->
    Loc = {loc, "foo.erl", 2, 3},
    ?assertEqual({ok, {ety, Loc, 1}}, attr:parse_ety_attr(Loc, "%-ety(1).")),
    ?assertEqual({ok, {ety, Loc, {foo, bar}}}, attr:parse_ety_attr(Loc, "%-ety({foo, bar}).")),
    ?assertEqual(no_attr, attr:parse_ety_attr(Loc, "%-xx({foo, bar}).")).
