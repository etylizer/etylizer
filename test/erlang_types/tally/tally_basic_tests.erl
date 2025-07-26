-module(tally_basic_tests).

-compile([nowarn_unused_function]). % ignore unused helper functions

-import(erlang_types_test_utils, [test_tally/2, test_tally/3, solutions/1]).

-include_lib("eunit/include/eunit.hrl").

% AST helper functions
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

tally_01_test() ->
  test_tally(
    [{v(alpha), tint()}],
    [{
      #{alpha => tnone()},
      #{alpha => tint()}
    }]
  ).

tally_01n_test() ->
  test_tally(
    [{b(), v(alpha)}, {v(alpha), tint()}],
    solutions(0)
  ).

tally_02_test() ->
  test_tally(
    [{tint(), v(alpha)}],
    [{
      #{alpha => tint()},
      #{alpha => tany()}
    }]
  ).

tally_03_test() ->
  test_tally(
    [
      {ttuple([]), v(zero)},
      {v(zero), ttuple([])}
    ],
    [{
      #{zero => ttuple([])},
      #{zero => ttuple([])}
    }]
  ).

tally_04_test() ->
  Alpha = v(alpha),
  Beta = v(beta),
  test_tally(
    [
      {Alpha, ttuple([tany()])},
      {ttuple([Beta]), Alpha},
      {tint(), Beta}
    ],
    [{
      #{alpha => ttuple([tint()]), beta => tint()},
      #{alpha => ttuple([tany()]), beta => tany()}
    }]
  ).


tally_05_test() ->
  Alpha = v(alpha),
  Beta = v(beta),
  test_tally(
    [
    {ttuple([Beta, {empty_list}]), Alpha}
  ],
    [{
      #{alpha => ttuple([Beta, {empty_list}])},
      #{alpha => tany() }
    }]
  ).

tally_05l_test() ->
  Alpha = v(alpha),
  Beta = v(beta),
  test_tally(
    [
    {tlist(Beta), Alpha}
  ],
    [{
      #{alpha => tlist(Beta)},
      #{alpha => tany() }
    }]
  ).

% debug tallying (['b] [ ('b, 'a2) ]);;
% result:[{'a2:='b}]
tally_06_test() ->
  Alpha = v(alpha),
  Beta = v(beta),
  test_tally(
    [{Beta, Alpha}],
    [{
      #{alpha => Beta},
      #{alpha => tany()}
    }],
    [beta]).

% debug tallying (['b] [ (['b*], 'a2) ]);;
% result:[{'a2:=[ 'b* ]}]
tally_07_test() ->
  Alpha = v(alpha),
  Beta = v(beta),
  test_tally(
    [
    {tlist(Beta), Alpha}
  ],
    [{
      #{alpha => tlist(Beta)},
      #{alpha => tany() }
    }],
    [beta]).

% see #36
% # debug tallying ([] [(1|2, 'alpha) ( (Int -> Int) & ((1|2) -> (1|2)), 'alpha -> 'beta) ('beta, 1|2)]);;
% [DEBUG:tallying]
% Result:[{'beta:=1--2 | 1--2 & 'a6a6; 'alpha:=1--2 | 1--2 & 'a6a6}]
tally_08_test() ->
  Alpha = v(alpha),
  Beta = v(beta),
  OneOrTwo = u(tint(1), tint(2)),
  OneOrTwoRange = tint(1, 2),
  test_tally(
    [
      {OneOrTwo, Alpha},
      {Beta, OneOrTwo},
      {i(f([tint()], tint()), f([OneOrTwo], OneOrTwo)), f([Alpha], Beta)}
    ],
    [{
      #{alpha => OneOrTwoRange, beta => OneOrTwoRange},
      #{alpha => OneOrTwoRange, beta => OneOrTwoRange}
    }]).

tally_08a_test() ->
  Alpha = v(alpha),
  test_tally(
    [
      {tint(1), Alpha},
      {f([tint()], tint()), f([Alpha], tint())}
    ],
    solutions(1)).

% Also see #36 (pl-git)
% #debug tallying ([] [( ((Int, Int) -> Int) & ((Int, Float) -> Float) & ((Float, Int) -> Float) & ((Float, Float) -> Float), ('alpha, 'beta) -> 'gamma ) (Int \ (1--2), 'alpha) (1, 'beta) (1, 'delta) (2, 'delta) ('delta, Int) ('gamma, 'delta)]);;
% [DEBUG:tallying]
% Result:[{
%  'gamma:=Int;
%  'delta:=Int;
%  'beta:=1 | Int & 'betabeta;
%  'alpha:=*--0 | 3--* | Int & 'alphaalpha
% }]
tally_09_test() ->
    Alpha = v(alpha),
    Beta = v(beta),
    Gamma = v(gamma),
    Delta = v(delta),
    One = tint(1),
    Two = tint(2),
    OneOrTwo = u(One, Two),
    I = tint(),
    F = tfloat(),
    test_tally(
      [{i([f([I, I], I), f([I, F], F), f([F, I], F), f([F, F], F)]), f([Alpha, Beta], Gamma)},
       {i(I, n(OneOrTwo)), Alpha},
       {One, Beta},
       {One, Delta},
       {Two, Delta},
       {Delta, I},
       {Gamma, Delta}],

      [{
        #{alpha => u(u([tint(3, '*')]), u([tint('*', 0)])),
          beta => tint(1, 1),
          gamma => I,
          delta => I },
        #{alpha => tint(),
          beta => tint(),
          gamma => I,
          delta => I }
      }]
    ).

tally_10_test() ->
    V0 = v(v0), V2 = v(v2), V3 = v(v3),
    V4 = v(v4), V5 = v(v5), V6 = v(v6),
    V7 = v(v7), V8 = v(v8),
    A = b(a), B = b(b),
    TupleAny = ttuple([tany()]),
    LargeInter = i([V0, n(i([ttuple([A]), TupleAny])), ttuple([B]), TupleAny]),
    test_tally(
      [{i([V0, ttuple1(A), TupleAny]), ttuple1(V3)},
       {u([i([ttuple1(A), TupleAny]), i([ttuple1(B), TupleAny])]), ttuple1(V8)},
       {ttuple1(V2), V0},
       {LargeInter, ttuple1(V8)},
       {LargeInter, ttuple1(V7)},
       {LargeInter, ttuple1(V6)},
       {i([V0, ttuple1(A), TupleAny]), ttuple1(V5)},
       {A, V2},
       {i([V0, ttuple1(A), TupleAny]), ttuple1(V4)}],
      [{#{}, #{}}]).

% debug tallying ([] [] [('a1 -> 'a2, 'a0) ('a4, 'a2) (42, 'a4) ('a3 & Int, 'a4) ('a3 & Int, 'a5) (Any -> Bool, 'a5 -> 'a6) ('a6, Bool) ('a1, 'a3)]);;
%[DEBUG:tallying]
%Result:[
%   {
%      'a1:=('a1a1 & 'a3a3) \ Int;
%      'a3:='a3a3 \ Int;
%      'a6:=Bool & 'a6a6;
%      'a5:=Empty;
%      'a4:=42 | 'a4a4 & 'a2a2;
%      'a2:=42 | 'a2a2;
%      'a0:=(('a1a1 & 'a3a3) \ Int -> 42 | 'a2a2) | 'a0a0};
%   {
%      'a1:=Int & 'a5 & 'a1a1 & 'a3a3 & 'a4a4 & 'a2a2 | 42 & 'a5 & 'a1a1 & 'a3a3 | ('a1a1 & 'a3a3) \ Int;
%      'a3:=Int & 'a5 & 'a3a3 & 'a4a4 & 'a2a2 | 42 & 'a5 & 'a3a3 | 'a3a3 \ Int;
%      'a6:=Bool;
%      'a4:=42 | 'a4a4 & 'a2a2;
%      'a2:=42 | 'a2a2;
%      'a0:=(Int & 'a5 & 'a1a1 & 'a3a3 & 'a4a4 & 'a2a2 | 42 & 'a5 & 'a1a1 & 'a3a3 | ('a1a1 & 'a3a3) \ Int -> 42 | 'a2a2) | 'a0a0
%   }]
tally_issue_8_test() ->
  A0 = v(alpha0), A1 = v(alpha1), A2 = v(alpha2), A3 = v(alpha3), A4 = v(alpha4), A5 = v(alpha5), A6 = v(alpha6),
  test_tally(
    [
      {f([A1], A2), A0},
      {A4, A2},
      {tint(42), A4},
      {i([A3, tint()]), A4},
      {i([A3, tint()]), A5},
      {f([tany()], tbool()), f([A5], A6)},
      {A6, tbool()},
      {A1, A3}
    ],
    [
      {
        #{ alpha2 => tint(42), alpha1 => tnone(), alpha3 => tnone(), alpha6 => tbool(), alpha4 => tint(42) },
        #{ alpha2 => tany(), alpha1 => tany(), alpha3 => tany(), alpha6 => tbool(), alpha4 => tany() }
      },
      {
        #{ alpha0 => f([tany()], tint(42)), alpha5 => tnone(), alpha2 => tint(42), alpha1 => tnone(), alpha3 => tnone(), alpha6 => tnone(), alpha4 => tnone() },
        #{ alpha0 => tany(), alpha5 => tnone(), alpha2 => tany(), alpha1 => i([tany(), n(tint())]), alpha3 => i([tany(), n(tint())]), alpha6 => tbool(), alpha4 => tany() }
      }
    ]).


tally_issue_14_test() ->
  V0 = v(v0), V2 = v(v2), V3 = v(v3), V4 = v(v4), V5 = v(v5),
  V6 = v(v6), V7 = v(v7), V8 = v(v8), A = b(a), B = b(b),
  TupleAny = ttuple1(tany()),
  LargeInter = i([V0, n(i([ttuple1(A), TupleAny])), ttuple1(B), TupleAny]),
  test_tally(
    [{i([V0, ttuple1(A), TupleAny]), ttuple1(V3)},
      {u([i([ttuple1(A), TupleAny]), i([ttuple1(B), TupleAny])]), ttuple1(V8)},
      {ttuple1(V2), V0},
      {LargeInter, ttuple1(V8)},
      {LargeInter, ttuple1(V7)},
      {LargeInter, ttuple1(V6)},
      {i([V0, ttuple1(A), TupleAny]), ttuple1(V5)},
      {A, V2},
      {i([V0, ttuple1(A), TupleAny]), ttuple1(V4)}],
    solutions(1)).


% constraints:
% { {$2},  $0 }
% { ($0 /\ not({a} /\ {any()})) /\ ({b} /\ {any()}), {$6} }
% { ($0 /\ not({a} /\ {any()})) /\ ({b} /\ {any()}), {$5} }
% { a, $2},
% {$0, {a} /\ {any()} | {b} /\ {any()}},
% {$0 /\ ({a} /\ {any()}), {$4}},
% {$0 /\ ({a} /\ {any()}), {$3}}]}
%
% cduce
% debug tallying (['a0 'a1 'a2 'a3 'a4 'a5 'a6] [] [
% (('a2, 42), 'a0)
% ('a0 & (`b, 42) \ (`a, 42), ('a6, 42))
% ('a0 & (`b, 42) \ (`a, 42), ('a5, 42))
% (`a, 'a2)
% ('a0, (`a, 42) | (`b, 42))
% (('a0 & (`a, 42)), ('a4, 42))
% (('a0 & (`a, 42)), ('a3, 42))
% ]);;
% Result:
% [{
%   'a0:=(`b & 'a5 & 'a6 & 'a2a2,42) | (`b & 'a5 & 'a6 & 'a2a2 & 'a3a3 & 'a4a4,42) | (`a,42) | ((`b & 'a5 & 'a6,42) | (`b & 'a5 & 'a6 & 'a3a3 & 'a4a4,42) | (`a,42)) & 'a0a0;
%   'a2:=`a | `b & 'a5 & 'a6 & 'a2a2 | (`b | `a) & 'a5 & 'a6 & 'a2a2 & 'a3a3 & 'a4a4;
%   'a3:=`a | 'a3a3;
%   'a4:=`a | 'a4a4
% }]
tally_foo2_test() ->
  % (('a2, 42), 'a0)
  C1 = {{tuple,[{var,'$2'}, {singleton, tag}]},{var,'$0'}},
  % (`a, 'a2)
  C2 = {{singleton,a},{var,'$2'}},
  % (('a0 & (`a, 42)), ('a4, 42))
  C3 = {
    {intersection,[ {var,'$0'}, {tuple,[{singleton,a}, {singleton, tag}]} ]},
    {tuple,[{var,'$4'}, {singleton, tag}]}
  },
  % (('a0 & (`a, 42)), ('a3, 42))
  C4 = {
    {intersection,[{var,'$0'}, {tuple,[{singleton,a}, {singleton, tag}]}]},
    {tuple,[{var,'$3'}, {singleton, tag}]}
  },
  % ('a0, (`a, 42) | (`b, 42))
  C5 = {
    {var,'$0'},
    {union,[
      {tuple,[{singleton,a}, {singleton, tag}]},
      {tuple,[{singleton,b}, {singleton, tag}]}
    ]}
  },
  % ('a0 & (`b, 42) \ (`a, 42), ('a6, 42))
  C6 = {
    {intersection, [
      {var,'$0'},
      {negation, {tuple,[{singleton,a}, {singleton, tag}]} },
      {tuple,[{singleton,b}, {singleton, tag}]}
    ]},
    {tuple,[{var,'$6'}, {singleton, tag}]}},

  % ('a0 & (`b, 42) \ (`a, 42), ('a5, 42))
  C7 = {
    {intersection, [
      {var,'$0'},
      {negation, {tuple,[{singleton,a}, {singleton, tag}]}},
      {tuple,[{singleton,b}, {singleton, tag}]}
    ]},
    {tuple,[{var,'$5'}, {singleton, tag}]}
  },

  test_tally(
    [
      C1, C2, C3, C4, C5, C6, C7
    ],
    [
      {
        #{'$0' => ttuple([b(a), b(tag)])                             , '$2' => b(a)           , '$3' => b(a)  , '$4' => b(a) },
        #{'$0' => u([ttuple([b(a), b(tag)]), ttuple([b(b), b(tag)])]), '$2' => u([b(a), b(b)]), '$3' => tany(), '$4' => tany()}
      }
    ]).

tally_fun_cons_test() ->
  A1 = v(a1), A2 = v(a2),
  A3 = v(a3), A4 = v(a4),

  test_tally(
    [
      {tempty_list(), A1},
      {tempty_list(), A2},
      {A3, tlist(tint())},
      {f([A4, A4], A4), f([A1, A2], A3)}
    ],
    solutions(1)).

tally_fun_cons3_test() ->
  test_tally(
    [
      {{empty_list},{var,'$3'}},
      {{var,'$0'},{intersection,[{tuple,[]},{tuple,[]}]}},
      {{var,'$1'},{list,{predef,integer}}},
      {{fun_full,[{list,{intersection,[{var,a@0},{predef,any}]}},
        {list,{intersection,[{var,a@0},{predef,any}]}}],
        {list,{intersection,[{var,a@0},{predef,any}]}}},
        {fun_full,[{var,'$2'},{var,'$3'}],{var,'$4'}}},
      {{empty_list},{var,'$2'}},
      {{var,'$4'},{var,'$1'}},
      {{intersection,[{var,'$0'},{intersection,[{tuple,[]},{tuple,[]}]}]},
        {tuple,[]}},
      {{tuple,[]},{var,'$0'}}
    ],
    solutions(1)).

pretty_printing_bug_test() ->
  V0 = v(v1), V6 = v(v2),
  A = b(a), B = b(b),
  test_tally(
    [{
      i([V0, n(ttuple1(A)), ttuple1(B)]),
      V6
    }],
    solutions(1)).
  
