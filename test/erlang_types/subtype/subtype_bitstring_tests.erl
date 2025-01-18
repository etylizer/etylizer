-module(subtype_bitstring_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tyscm/2, tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tint/1, tunion/1, tintersect/1, trange_any/0, tint/0, ttuple/1, tany/0, tnone/0, tmap/1, tmap_any/0, tmap_field_req/2, tmap_field_opt/2]).
-import(test_utils, [is_subtype/2, is_equiv/2, named/2]).


bitstring_test() ->
  true = is_equiv({bitstring}, {bitstring}).

bitstring_neg_test() ->
  false = is_subtype({bitstring}, tnegate({bitstring})).