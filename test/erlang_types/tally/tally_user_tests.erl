-module(tally_user_tests).

-compile([nowarn_unused_function]). % ignore unused helper functions

-import(erlang_types_test_utils, [test_tally_satisfiable/4, test_tally/2, test_tally/3, test_tally/4, solutions/1]).

-include_lib("eunit/include/eunit.hrl").

% AST helper functions
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").
                

% #201
% type M('k, 'v) =  (('k, 'v), Empty -> Any);;
% debug tallying ([] ['k 'v] [ ( M('k, 'v) , (('a0, 'a1), Empty -> Any) ) ('k, 'a0) ((`ok, 'a1) | `error, (`ok, 'v) | `error) ]);;
% Result:  [{'a1:='v | 'a1a1; 'a0:='k | 'a0a0}]
% Cleaned: [{'a1:='v        ; 'a0:='k}]
maps_issue_201_test() ->
  {K, V} = {v(k), v(v)},
  L = tmap([ tmap_field_opt(K, V) ]),
  R = tmap([ tmap_field_opt(v(alpha_0), v(alpha_1)) ]),

  Sym = [{test_key(t, 2), tyscm([k, v], L)}],
  
  test_tally(
    [
      % {scsubty, 14:21, {ok, $1} | error, {ok, V} | error},
      {u([ttuple([tatom(ok), v('alpha_1')]), tatom(error)]), u([ttuple([tatom(ok), V]), tatom(error)])}, 
      % {scsubty, 14:31, K, $0},
      {K, v(alpha_0)}, 
      % {scsubty, 14:36, t(K, V), #{$0 => $1}}]
      {tnamed(t, [K, V]), R}
    ],
    solutions(1),
    % Fixed: K, V
    [k, v],
    Sym
  ).

issue_226_test() ->
  GuardTest = tnamed(gen_tuple, [tnamed(guard_test, [])]),
  GenTuple = ttuple([tlist(v('T'))]),

  Sym = [
    {test_key(guard_test), tyscm([], GuardTest)},
    {test_key(gen_tuple, 1), tyscm([t], GenTuple)}
  ],

  test_tally_satisfiable(
    true,
    [ {tnamed(guard_test, []), v(some_var)} ],
    [],
    Sym
  ).
  
