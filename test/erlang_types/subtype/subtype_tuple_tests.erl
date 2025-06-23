-module(subtype_tuple_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

empty_tuples_edge_cases_test() ->
  S = ttuple([]),
  T = ttuple([tany()]),
  true = is_subtype(S, S),
  false = is_subtype(S, T),
  false = is_subtype(T, S),
  true = is_subtype(S, ttuple_any()),
  false = is_subtype(ttuple_any(), S),
  ok.

tuple_1_test() ->
  S = ttuple([b(a), b(b)]),
  T = ttuple([tany(), tany()]),
  true = is_subtype(S, T),
  false = is_subtype(T, S).

tuple_2_test() ->
  S = ttuple([b(a)]),
  T = ttuple([tany(), tany()]),
  false = is_subtype(S, T),
  false = is_subtype(T, S).

empty_tuple_test() ->
  O2 = i(ttuple([b(b)]), ttuple([b(a)])),
  true = is_subtype(O2, tempty()).

simple_prod_var_test() ->
  S = ttuple([b(hello)]),
  T = ttuple([v(alpha)]),
  false = is_subtype(S, T),
  false = is_subtype(T, S).

var_prod_test() ->
  S = i(ttuple([b(hello)]), v(alpha)),
  T = v(alpha),
  true = is_subtype(S, T),
  false = is_subtype(T, S),
  ok.

neg_var_prod_test() ->
  S = ttuple([b(hello), v(alpha)]),
  T = v(alpha),
  false = is_subtype(S, T),
  false = is_subtype(T, S),
  ok.

pos_var_prod_test() ->
  S = i(ttuple([b(hello)]), v(alpha)),
  T = n(v(alpha)),
  false = is_subtype(S, T),
  false = is_subtype(T, S),
  ok.

var_subsumption_test() ->
  S = u(
    i(ttuple([b(hello)]), v(alpha)),
    ttuple([b(hello)])
  ),
  T = ttuple([b(hello)]),
  true = is_subtype(S, T),
  true = is_subtype(T, S),
  ok.

var_subsumption_2_test() ->
  S = i(
    u(
      n(ttuple([b(hello)])),
      i(ttuple([tany()]), v(beta))
    ),
    n(ttuple([b(hello)])) 
  ),
  T = n(ttuple([b(hello)])),
  true = is_subtype(S, T),
  true = is_subtype(T, S),
  ok.

var_subsumption_3_test() ->
  % alpha & !beta & SomeTuple < alpha & SomeTuple
  S = i(ttuple([b(a)]), v(alpha)),
  T = i(
    ttuple([b(a)]), 
    i(
      n(v(beta)), 
      v(alpha)
    )
  ),
  false = is_subtype(S, T),
  true = is_subtype(T, S),
  ok.
