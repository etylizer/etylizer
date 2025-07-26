-module(tally_varorder_tests).

-compile([nowarn_unused_function]). % ignore unused helper functions

-import(erlang_types_test_utils, [test_tally/2, test_tally/3, solutions/1]).

-include_lib("eunit/include/eunit.hrl").

% AST helper functions
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

sol_number_test() ->
  % changing variable order produces a different number of solutions

  % ('a2, 42) <=  ('a1, 42)
  C1 = { ttuple([v('$2'), b(tag)]), ttuple([v('$1'), b(tag)])},
  % ('a1, 42) <=  ('a2, 42)
  C2 = { ttuple([v('$1'), b(tag)]), ttuple([v('$2'), b(tag)])},

  % single solution variable order says
  % 'a2 is replaced by 'a1 & 'mu1

  % multiple solution variable order says
  % EITHER    'a2 is empty
  % OR        'a1 is replaced by 'a2 U 'mu1
  % both tally results are equivalent

  % variable order determines if a variable is used as a lower or upper bound for another variable
  test_tally( [ C2 ], solutions(1)),
  test_tally( [ C1 ], solutions(2)).

good_variable_order_tuples_test() ->
  % tuples: if variables on the left side of a constraint are lower order, number of solutions decreases
  C1 = { ttuple([v('$0')]), 
         i([
          ttuple([v('$4')]),
          ttuple([v('$3')]),
          ttuple([v('$2')]),
          ttuple([v('$1')])
         ])
       },

  % if bigger, then solutions amount increases. 
  % The more variables there are on the right side, the more solutions, if no DNF minimization is implemented
  C2 = { ttuple([v('$5')]), 
         i([
          ttuple([v('$4')]),
          ttuple([v('$3')]),
          ttuple([v('$2')]),
          ttuple([v('$1')])
         ])
       },

  test_tally( [ C1 ], solutions(1)),
  test_tally( [ C2 ], solutions(2)), % was 5 before
  ok.

% if we don't have minimization, the variable order creates a different evaluation of the BDD where sometimes 
% more solutions are calculated than necessary
% example:          v5 & ~v2      | v5 &  v2 & ~v1 
% is equivalent to: v5 & ~v2 & v1 | v5       & ~v1
% if there are more terms in a line than necessary (which might contain more variable), 
% this bloats the normalization result with unecessary variables
% and non-subsumable constraint sets
bdd_order_matters_test() ->
  C1 = { ttuple([v('$5')]), i([ ttuple([v('$2')]), ttuple([v('$1')]) ]) },
  C2 = { ttuple([v('$5')]), i([ ttuple([v('$1')]), ttuple([v('$2')]) ]) },

  % before the DNF minimization of a BDD -> DNF call, this call created 3 solutions
  test_tally( [ C1 ], solutions(2)),
  test_tally( [ C2 ], solutions(2)),
  ok.
