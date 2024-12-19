-module(subtype_tuple_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tyscm/2, tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tint/1, tunion/1, tintersect/1, trange_any/0, tint/0, ttuple/1, tany/0, tnone/0, tmap/1, tmap_any/0, tmap_field_req/2, tmap_field_opt/2]).
-import(test_utils, [is_subtype/2, is_equiv/2, named/2]).

i(A,B) -> stdtypes:tintersect([A,B]).

empty_tuples_edge_cases_test() ->
  S = stdtypes:ttuple([]),
  T = stdtypes:ttuple([stdtypes:tany()]),
  true = is_subtype(S, S),
  false = is_subtype(S, T),
  false = is_subtype(T, S),
  true = is_subtype(S, stdtypes:ttuple_any()),
  false = is_subtype(stdtypes:ttuple_any(), S),
  ok.

tuple_1_test() ->
  S = ttuple([tatom(a), tatom(b)]),
  T = ttuple([tany(), tany()]),
  true = is_subtype( S, T ),
  false = is_subtype( T, S ).

tuple_2_test() ->
  S = {tuple, [tatom(a)]},
  T = {tuple, [{predef, any}, {predef, any}]},
  false = is_subtype( S, T ),
  false = is_subtype( T, S ).

empty_tuple_test() ->
  O2 = {intersection,
    [
      {tuple, [tatom(b)]},
      {tuple,[tatom(a)]}
    ]},

  true = subty:is_empty(O2, symtab:empty()),
  ok.

simple_prod_var_test() ->
  S = stdtypes:ttuple([stdtypes:tatom(hello)]),
  T = stdtypes:ttuple([stdtypes:tvar(alpha)]),

  false = is_subtype( S, T ),
  false = is_subtype( T, S ),
  ok.

var_prod_test() ->
  S = i(stdtypes:ttuple([stdtypes:tatom(hello)]), stdtypes:tvar(alpha)),
  T = stdtypes:tvar(alpha),

  true = is_subtype( S, T ),
  false = is_subtype( T, S ),
  ok.

neg_var_prod_test() ->
  S = stdtypes:ttuple([stdtypes:tatom(hello), stdtypes:tvar(alpha)]),
  T = stdtypes:tvar(alpha),

  false = is_subtype( S, T ),
  false = is_subtype( T, S ),
  ok.

pos_var_prod_test() ->
  S = i(stdtypes:ttuple([stdtypes:tatom(hello)]), stdtypes:tvar(alpha)),
  T = stdtypes:tnegate(stdtypes:tvar(alpha)),

  false = is_subtype( S, T ),
  false = is_subtype( T, S ),
  ok.