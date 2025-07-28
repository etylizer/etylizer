-module(tally_config_tests).

-import(erlang_types_test_utils, [loc_auto/0, with_symtab/2, test_tally_satisfiable/2, test_tally_satisfiable/4]).

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

% bug?
mk_negation_bug_test() ->
  % {ok, [Cons1]} = file:consult("test_files/erlang_types/tally/mkdiff_1.config"),
  % {ok, [System1]} = file:consult("test_files/erlang_types/tally/mkdiff_1.system"),
  {ok, [Cons2]} = file:consult("test_files/erlang_types/tally/mkdiff_2.config"),
  {ok, [System2]} = file:consult("test_files/erlang_types/tally/mkdiff_2.system"),
  % test_tally_satisfiable(true, Cons1, [], maps:to_list(System1)),
  test_tally_satisfiable(false, Cons2, [], maps:to_list(System2)).


mk_negation_cache_bug_test() ->
  {ok, [Symtab]} = file:consult("test_files/erlang_types/tally/mkdiff_1.system"),
  {ok, [Cons1]} = file:consult("test_files/erlang_types/tally/mkdiff_1.config"),
  {ok, [Cons2]} = file:consult("test_files/erlang_types/tally/mkdiff_2.config"),


  with_symtab(fun() ->
    Constrs1 = 
      sets:from_list(
        lists:map( 
          fun ({T, U}) -> {scsubty, sets:from_list([loc_auto()]), T, U} end,
          Cons1
      )),
    Constrs2 = 
      sets:from_list(
        lists:map( 
          fun ({T, U}) -> {scsubty, sets:from_list([loc_auto()]), T, U} end,
          Cons2
      )),

    {true, _} = tally:is_satisfiable(symtab:empty(), Constrs1, sets:from_list([])),
    {false, _} = tally:is_satisfiable(symtab:empty(), Constrs2, sets:from_list([])),
    ok
              end,
    Symtab).
