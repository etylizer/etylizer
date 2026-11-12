-module(tally_bitstring_tests).

-compile([nowarn_unused_function]). % ignore unused helper functions

-import(erlang_types_test_utils, [test_tally/2, solutions/1]).

-include_lib("eunit/include/eunit.hrl").

% AST helper functions
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

bitstring_01_test() ->
  test_tally(
    [{tbitstring(), tbitstring()}],
    solutions(1)
  ).

% binary <= alpha, alpha <= bitstring => alpha in [binary..bitstring]
binary_leq_var_leq_bitstring_test() ->
  test_tally(
    [{tbinary(), v(alpha)}, {v(alpha), tbitstring()}],
    [{
      #{alpha => tbinary()},
      #{alpha => tbitstring()}
    }]
  ).

% bitstring <= alpha, alpha <= binary => unsatisfiable
bitstring_leq_var_leq_binary_unsat_test() ->
  test_tally(
    [{tbitstring(), v(alpha)}, {v(alpha), tbinary()}],
    solutions(0)
  ).
