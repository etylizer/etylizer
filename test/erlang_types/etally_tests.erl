-module(etally_tests).
-include_lib("eunit/include/eunit.hrl").

-import(test_ast, [norm_css_basic/1, norm_substs/1, norm/1, mu/2, n/1, b/0, b/1, f/2, t/1, t/2, i/2, i/1, u/2, u/1, r/1, r/0, none/0, any/0, v/1, subty/2, normalize/3, normalize/2, var_of/1, norm_css/1]).

% TODO think about how to test tally equivalent solutions

%%example_merge_test() ->
%%  C1 = {norm(f(v(alpha), b(bool))), norm(f(v(beta), v(beta)))},
%%  C2 = {norm(f(u(r(), b(bool)), r())), norm(f(v(alpha), v(beta)))},
%%  X = tally:tally([C1, C2]),
%%  [Z1, Z2] = X,
%%
%%  [{_V1, _T1}, {_V2, _T2}] = Z1,
%%  [{_V3, _T3}, {_V4, _T4}] = Z2,
%%
%%  ok.
%%
%%example_merge2_test() ->
%%  C1 = {norm(f(v(alpha), b(bool))), norm(f(v(beta), v(beta)))},
%%  C2 = {norm(t(r(), r())), norm(f(v(alpha), v(beta)))},
%%  _Res = tally:tally([C1, C2]),
%%  ok.
%%
%% issue_8_tally_test() ->
%%   % fix order for variables
%%   lists:foreach(fun(Atom) -> norm(v(Atom)) end, ['0','1','2','3','4','5','6']),
%%   C1 = {norm(f(v('1'), v('2'))), norm(v('0'))},
%%   C2 = {norm(v('4'))           , norm(v('2'))},
%%   C3 = {norm(r(42))            , norm(v('4'))},
%%   C4 = {norm(v('3'))           , norm(any())},
%%   C5 = {norm(i(v('3'), r()))   , norm(v('4'))},
%%   C6 = {norm(i(v('3'), r()))   , norm(v('5'))},
%%   C7 = {norm(f(any(), b(bool))), norm(f(v('5'), v('6')))},
%%   C8 = {norm(v('6'))           , norm(b(bool))},
%%   C9 = {norm(v('1'))           , norm(v('3'))},
%% 
%%   Res = tally:tally([C1, C2, C3, C4, C5, C6, C7, C8, C9]),
%% 
%%   [_Sub1, _Sub2] = Res,
%% 
%%   ok.
%%
%%issue_13_tally_test() ->
%%  A = b(a),
%%  B = b(b),
%%  D = b(dummy),
%%  TAny = t(any(), any()),
%%  LargeInter = i([
%%    v(v0),
%%    n(i([t(A, D), TAny])),
%%    t(B, D),
%%    TAny
%%  ]),
%%
%%  C1 = { i([v(v0), t(A, D), t(any(), any())]),  t(v(v3), D) },
%%  C2 = { u([ i(t(A, D), TAny), i(t(B, D), TAny) ]), t(v(v8), D) },
%%  C3 = { t(v(v2), D), v(v0)},
%%  C4 = { LargeInter, t(v(v8), D)},
%%  C5 = { LargeInter, t(v(v7), D)},
%%  C6 = { LargeInter, t(v(v6), D)},
%%  C7 = { A, v(v2)},
%%  C8 = { i([v(v0), t(A, D), TAny]),t(v(v5), D)},
%%  C9 = { i([v(v0), t(A, D), TAny]),t(v(v4), D)},
%%
%%  % fix order for variables
%%%%  lists:foreach(fun(Atom) -> norm(v(Atom)) end, ['0','1','2','3','4','5','6']),
%%
%%  _Res = tally:tally(norm_all([C1, C2, C3, C4, C5, C6, C7, C8, C9])),
%%
%%%%  io:format(user, "Res: ~n~p~n", [Res]),
%%
%%  ok.

issue_test() ->
  C1 = {r(), v(a1)},
  C2 = {t([v(a1)]), t([v(a2)])},
  C3 = {v(a2), b()},
  {error, _} = tally:tally(norm_all([C1, C2, C3])),
  ok.

% issue2_test() ->
%   C1 = {t([v(a2)]), v(a0)},
%   C2 = {v(a0), u([
%                   t([b(a)])
%                   , 
%                   t([b(b)])
%                  ])},
%   C3 = {b(a), v(a2)},
%   C4 = {i([v(a0), t([b(a)])]), t([v(a4)])},
%   C5 = {i([v(a0), t([b(a)])]), t([v(a3)])},
%   C6 = {
%     i([v(a0), t([b(b)]), n(t([b(a)]))]),
%     t([v(a6)])
%    },
%   C7 = {
%     i([v(a0), t([b(b)]), n(t([b(a)]))]),
%     t([v(a5)])
%    },
% 
% 
%   Res = tally:tally(norm_all([C1, C2, C3, C4, C5, C6, C7])),
%   ok.

norm_all(List) ->
  lists:map(fun({S, T}) -> {norm(S), norm(T)} end, List).
