-module(tally_config_tests).

-import(erlang_types_test_utils, [test_tally_satisfiable/2, test_tally_satisfiable/4]).

-include_lib("eunit/include/eunit.hrl").

plus_test() ->
  {ok, [Cons]} = file:consult("test_files/tally/plus_chained.config"),
  test_tally_satisfiable(true, Cons).

fun_local_02_test() ->
  {ok, [Cons]} = file:consult("test_files/tally/fun_local_02.config"),
  test_tally_satisfiable(true, Cons).

tatom_test() ->
  {ok, [Cons]} = file:consult("test_files/tally/tatom.config"),
  {ok, [System]} = file:consult("test_files/tally/tatom.system"),
  test_tally_satisfiable(true, Cons, [], maps:to_list(System)).

recursive_test() ->
  {ok, [Cons]} = file:consult("test_files/tally/user_07.config"),
  test_tally_satisfiable(true, Cons).

