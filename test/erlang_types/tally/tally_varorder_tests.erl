-module(tally_varorder_tests).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, tfun1/2, trange/2,
                   tunion/1, tunion/2, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0,
                   tint/0, tint/1, ttuple1/1, tinter/1, tinter/2, tlist/1, tempty_list/0,
                   tfloat/0, tfun2/3, tnot/1, tbool/0,
                   tmap/1, tmap_any/0, tmap_field_opt/2, tmap_field_req/2
                  ]).


sol_number_test() ->
  % changing variable order produces a different number of solutions

  % ('a2, 42) <=  ('a1, 42)
  C1 = { {tuple,[{var,'$2'}, {singleton, tag}]}, {tuple,[{var,'$1'}, {singleton, tag}]}},
  % ('a1, 42) <=  ('a2, 42)
  C2 = { {tuple,[{var,'$1'}, {singleton, tag}]}, {tuple,[{var,'$2'}, {singleton, tag}]}},

  % single solution variable order says
  % 'a2 is replaced by 'a1 & 'mu1

  % multiple solution variable order says
  % EITHER    'a2 is empty
  % OR        'a1 is replaced by 'a2 U 'mu1
  % both tally results are equivalent

  % variable order determines if a variable is used as a lower or upper bound for another variable
  test_utils:test_tally( [ C2 ], test_utils:solutions(1)),
  test_utils:test_tally( [ C1 ], test_utils:solutions(2)).
