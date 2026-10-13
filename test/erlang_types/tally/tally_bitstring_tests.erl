-module(tally_bitstring_tests).

-compile([nowarn_unused_function]). % ignore unused helper functions

-import(erlang_types_test_utils, [test_tally/2, test_tally/3, solutions/1]).

-include_lib("eunit/include/eunit.hrl").

% AST helper functions
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

% === Basic satisfiability ===

% bitstring <= bitstring (trivially satisfiable)
bitstring_01_test() ->
  test_tally(
    [{tbitstring(), tbitstring()}],
    solutions(1)
  ).

% binary <= bitstring (satisfiable)
binary_subtype_bitstring_test() ->
  test_tally(
    [{tbinary(), tbitstring()}],
    solutions(1)
  ).

% binary <= binary (satisfiable)
binary_subtype_binary_test() ->
  test_tally(
    [{tbinary(), tbinary()}],
    solutions(1)
  ).

% bitstring <= binary (NOT satisfiable - non-byte-aligned part doesn't fit)
bitstring_not_subtype_binary_test() ->
  test_tally(
    [{tbitstring(), tbinary()}],
    solutions(0)
  ).

% nonempty_binary <= binary (satisfiable)
nonempty_binary_subtype_binary_test() ->
  test_tally(
    [{tnonempty_binary(), tbinary()}],
    solutions(1)
  ).

% nonempty_bitstring <= binary (NOT satisfiable)
nonempty_bitstring_not_subtype_binary_test() ->
  test_tally(
    [{tnonempty_bitstring(), tbinary()}],
    solutions(0)
  ).

% empty_bitstring <= nonempty_binary (NOT satisfiable)
empty_not_subtype_nonempty_binary_test() ->
  test_tally(
    [{tempty_bitstring(), tnonempty_binary()}],
    solutions(0)
  ).

% === Variable solving: alpha <= bitstring ===

% alpha <= bitstring => alpha in [none..bitstring]
var_subtype_bitstring_test() ->
  test_tally(
    [{v(alpha), tbitstring()}],
    [{
      #{alpha => tnone()},
      #{alpha => tbitstring()}
    }]
  ).

% alpha <= binary => alpha in [none..binary]
var_subtype_binary_test() ->
  test_tally(
    [{v(alpha), tbinary()}],
    [{
      #{alpha => tnone()},
      #{alpha => tbinary()}
    }]
  ).

% === Variable solving: concrete <= alpha ===

% bitstring <= alpha => alpha in [bitstring..any]
bitstring_subtype_var_test() ->
  test_tally(
    [{tbitstring(), v(alpha)}],
    [{
      #{alpha => tbitstring()},
      #{alpha => tany()}
    }]
  ).

% binary <= alpha => alpha in [binary..any]
binary_subtype_var_test() ->
  test_tally(
    [{tbinary(), v(alpha)}],
    [{
      #{alpha => tbinary()},
      #{alpha => tany()}
    }]
  ).

% === Variable solving: bounded variables ===

% binary <= alpha, alpha <= bitstring => alpha in [binary..bitstring]
binary_leq_var_leq_bitstring_test() ->
  test_tally(
    [{tbinary(), v(alpha)}, {v(alpha), tbitstring()}],
    [{
      #{alpha => tbinary()},
      #{alpha => tbitstring()}
    }]
  ).

% nonempty_binary <= alpha, alpha <= binary => alpha in [nonempty_binary..binary]
nonempty_binary_leq_var_leq_binary_test() ->
  test_tally(
    [{tnonempty_binary(), v(alpha)}, {v(alpha), tbinary()}],
    [{
      #{alpha => tnonempty_binary()},
      #{alpha => tbinary()}
    }]
  ).

% bitstring <= alpha, alpha <= binary => unsatisfiable
bitstring_leq_var_leq_binary_unsat_test() ->
  test_tally(
    [{tbitstring(), v(alpha)}, {v(alpha), tbinary()}],
    solutions(0)
  ).

% nonempty_bitstring <= alpha, alpha <= binary => unsatisfiable
nonempty_bitstring_leq_var_leq_binary_unsat_test() ->
  test_tally(
    [{tnonempty_bitstring(), v(alpha)}, {v(alpha), tbinary()}],
    solutions(0)
  ).

% === Mixed bitstring/non-bitstring constraints ===

% integer <= alpha, alpha <= bitstring => unsatisfiable (disjoint types)
int_leq_var_leq_bitstring_unsat_test() ->
  test_tally(
    [{tint(), v(alpha)}, {v(alpha), tbitstring()}],
    solutions(0)
  ).

% empty_bitstring <= alpha, alpha <= nonempty_binary => unsatisfiable
empty_leq_var_leq_nonempty_binary_unsat_test() ->
  test_tally(
    [{tempty_bitstring(), v(alpha)}, {v(alpha), tnonempty_binary()}],
    solutions(0)
  ).

% === Multiple variables ===

% alpha <= binary, beta <= alpha => beta in [none..binary], alpha in [beta..binary]
two_vars_test() ->
  test_tally(
    [{v(alpha), tbinary()}, {v(beta), v(alpha)}],
    solutions(1)
  ).

% === Union constraints ===

% alpha <= binary | integer (should be satisfiable)
var_subtype_union_test() ->
  test_tally(
    [{v(alpha), u(tbinary(), tint())}],
    solutions(1)
  ).

% === Fixed-size bitstring types in constraints ===

% FIXME too slow
% <<_:32>> <= binary (satisfiable)
% fixed_32_subtype_binary_test() ->
%   test_tally(
%     [{tbitstring_m_n(32, 0), tbinary()}],
%     solutions(1)
%   ).

% <<_:5>> <= binary (NOT satisfiable)
fixed_5_not_subtype_binary_test() ->
  test_tally(
    [{tbitstring_m_n(5, 0), tbinary()}],
    solutions(0)
  ).

% <<_:5>> <= bitstring (satisfiable)
fixed_5_subtype_bitstring_test() ->
  test_tally(
    [{tbitstring_m_n(5, 0), tbitstring()}],
    solutions(1)
  ).
