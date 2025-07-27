-module(tally_config_tests).

-import(erlang_types_test_utils, [test_tally_satisfiable/2, test_tally_satisfiable/4]).

-include_lib("eunit/include/eunit.hrl").

% 2.7 -> 0.1
plus_test() ->
  {ok, [Cons]} = file:consult("test_files/erlang_types/tally/plus_chained.config"),
  test_tally_satisfiable(true, Cons).

% 3.2 -> 0.2
fun_local_02_test() ->
  {ok, [Cons]} = file:consult("test_files/erlang_types/tally/fun_local_02.config"),
  test_tally_satisfiable(true, Cons).

% 5.5 -> 1.1
tatom_test() ->
  {ok, [Cons]} = file:consult("test_files/erlang_types/tally/tatom.config"),
  {ok, [System]} = file:consult("test_files/erlang_types/tally/tatom.system"),
  test_tally_satisfiable(true, Cons, [], maps:to_list(System)).

% timeout -> 0.1
recursive_test() ->
  {ok, [Cons]} = file:consult("test_files/erlang_types/tally/user_07.config"),
  test_tally_satisfiable(true, Cons).

% timeout -> 2.0
std_union_test() ->
  {ok, [Cons]} = file:consult("test_files/erlang_types/tally/union.config"),
  {ok, [Fixed]} = file:consult("test_files/erlang_types/tally/union.fixed"),
  {ok, [System]} = file:consult("test_files/erlang_types/tally/union.system"),
  test_tally_satisfiable(true, Cons, Fixed, maps:to_list(System)).
