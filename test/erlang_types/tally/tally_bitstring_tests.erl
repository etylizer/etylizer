-module(tally_bitstring_tests).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, tfun1/2, trange/2,
                   tunion/1, tunion/2, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0,
                   tint/0, tint/1, ttuple1/1, tinter/1, tinter/2, tlist/1, tempty_list/0,
                   tfloat/0, tfun2/3, tnot/1, tbool/0,
                   tmap/1, tmap_any/0, tmap_field_opt/2, tmap_field_req/2
                  ]).

bitstring() -> {bitstring}.


bitstring_01_test() ->
  test_utils:test_tally(
    [{bitstring(), bitstring()}],
    test_utils:solutions(1)
  ).
