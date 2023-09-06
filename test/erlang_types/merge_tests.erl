-module(merge_tests).
-include_lib("eunit/include/eunit.hrl").

-import(test_ast, [norm_css_basic/1, norm_substs/1, norm/1, mu/2, n/1, b/0, b/1, f/2, t/2, i/2, i/1, u/2, u/1, r/1, r/0, none/0, any/0, v/1, subty/2, normalize/3, normalize/2, var_of/1, norm_css/1]).

% TODO this test case is dependent on the solution order and amount of constraint_set:merge_and_meet,
% think about a better way to test the result
example_merge_test() ->
  Res1 = normalize(f(v(alpha), b(bool)), f(v(beta), v(beta)), sets:new()),
  Res2 = normalize(f(u(r(), b(bool)), r()), f(v(alpha), v(beta)), sets:new()),
  Result = constraint_set:merge_and_meet(Res1, Res2),

  [C1, C2, C3, C4] = Result,
  % unchanged
  [C1] = constraint_set:saturate(C1, sets:new(), sets:new()),

  % unsat
  [] = constraint_set:saturate(C2, sets:new(), sets:new()),
  [] = constraint_set:saturate(C3, sets:new(), sets:new()),

  % new
  % {
  %   {(α,0),(β,0)} ,
  %   {(β,α),(α,Int∨Bool),(Int∨Bool,β),(β,Int∨Bool)}
  % }

%%  io:format(user, "Input:~n~p~n,", [C4]),
  [[_MC1, _MC2]] = constraint_set:saturate(C4, sets:new(), sets:new()),

%%  {MV1, Z1, Z2} = MC1,
%%  {MV2, Z3, Z4} = MC2,


  ok.
