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
