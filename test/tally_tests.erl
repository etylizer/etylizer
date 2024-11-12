-module(tally_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("../src/log.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, tfun1/2, trange/2,
                   tunion/1, tunion/2, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0,
                   tint/0, tint/1, ttuple1/1, tinter/1, tinter/2, tlist/1, tempty_list/0,
                   tfloat/0, tfun2/3, tnot/1, tbool/0,
                   tmap/1, tmap_any/0, tmap_field_opt/2, tmap_field_req/2
                  ]).


-type expected_subst() :: {
  #{ atom() => ast:ty() },  % lower bounds
  #{ atom() => ast:ty() } % upper bounds
}.

-spec test_tally(list({ast:ty(), ast:ty()}), list(expected_subst())) -> ok.
test_tally(ConstrList, ExpectedSubst) ->
    test_tally(ConstrList, ExpectedSubst, symtab:empty(), []).


-spec test_tally(list({ast:ty(), ast:ty()}), list(expected_subst()), [ast:ty_varname()]) -> ok.
test_tally(ConstrList, ExpectedSubst, FixedVars) ->
    test_tally(ConstrList, ExpectedSubst, symtab:empty(), FixedVars).

-spec test_tally(list({ast:ty(), ast:ty()}), list(expected_subst()), symtab:t(), [ast:ty_varname()]) -> ok.
test_tally(ConstrList, AllTests, Symtab, FixedVars) ->
  Constrs = sets:from_list(
                lists:map(
                  fun ({T, U}) -> {scsubty, sets:from_list([ast:loc_auto()]), T, U} end,
                  ConstrList
                 )),

  Res = tally:tally(Symtab, Constrs, sets:from_list(FixedVars)),
  case Res of
    [_ | _] -> 
      ?LOG_WARN("Tally result:~n~s",
        pretty:render_substs(lists:map(fun (S) -> subst:base_subst(S) end, Res))),
      find_subst(AllTests, Res, Res);
    _ -> 
      case AllTests of 
        [] -> ok;
        _ -> error(utils:sformat("Unexpected result from tally: ~w", Res))
      end
  end.

-spec find_subst(list(expected_subst()), [subst:t()], [subst:t()]) -> ok.
find_subst([], [], _) -> ok;
find_subst([{Low, High} | _], [], Sols) ->
  ?LOG_WARN("~nCould not find substitutions among remaining ~p tally solutions for~n" ++
    "expected lower bound:~n~s~n~nexpected upper bound:~n~s~n~nRemaining:~s",
            length(Sols),
            pretty:render_subst(Low),
            pretty:render_subst(High),
            pretty:render_substs(lists:map(fun (S) -> subst:base_subst(S) end, Sols))
  ),
  error("test failed because tally returned no substitution that matches low and high bounds");
find_subst([], [_X | _Xs], Remaining) ->
  Substs = lists:map(fun (S) -> subst:base_subst(S) end, Remaining),
  ?LOG_WARN("~nToo many substitutions return from tally. Unconsumed: ~200p", Substs),
  error("Too many substitutions returned from tally");
find_subst(X = [{Low, High} | OtherTests], [TallySubst | Others], AllTally) ->
  Subst = subst:base_subst(TallySubst),
  Valid = lists:any(
    fun({{Var, LowerBound}, {Var, UpperBound}}) ->
      begin
        TyOther = maps:get(Var, Subst, {var, Var}),
        not (subty:is_subty(none, LowerBound, TyOther) andalso
          subty:is_subty(none, TyOther, UpperBound))
      end
    end, lists:zip(lists:sort(maps:to_list(Low)), lists:sort(maps:to_list(High)))),
  case Valid of
    true -> find_subst(X, Others, AllTally);
    false -> find_subst(OtherTests, AllTally -- [TallySubst], AllTally -- [TallySubst])
  end.

solutions(Number) ->
  [{#{}, #{}} || _ <- lists:seq(1, Number)].

tally_01_test() ->
    test_tally(
      [{tvar(alpha), tint()}],
      [{
        #{ alpha => tnone()},
        #{ alpha => tint()}
      }]
    ).

tally_02_test() ->
    test_tally(
      [{tint(), tvar(alpha)}],
      [{
        #{ alpha => tint()},
        #{ alpha => tany()}
      }]
    ).

tally_03_test() ->
  test_tally(
    [
    {ttuple([]), tvar(zero)},
    {tvar(zero), ttuple([])}
  ],
    [{
      #{ zero => ttuple([])},
      #{ zero => ttuple([])}
    }]
  ).

tally_04_test() ->
    Alpha = tvar(alpha),
    Beta = tvar(beta),
    test_tally(
      [
      {Alpha, ttuple1(tany())},
      {ttuple1(Beta), Alpha},
      {tint(), Beta}
    ],
      [{
        #{ alpha => ttuple([tint()]), beta => tint()},
        #{ alpha => ttuple([tany()]), beta => tany()}
      }]
    ).

tally_05_test() ->
    Alpha = tvar(alpha),
    Beta = tvar(beta),
    test_tally(
      [
      {tlist(Beta), Alpha}
    ],
      [{
        #{ alpha => tlist(Beta)},
        #{ alpha => tany() }
      }]
    ).

% debug tallying (['b] [ ('b, 'a2) ]);;
% result:[{'a2:='b}]
tally_06_test() ->
    Alpha = tvar(alpha),
    Beta = tvar(beta),
    test_tally(
      [{Beta, Alpha}],
      [{
        #{ alpha => Beta },
        #{ alpha => tany() }
      }],
      [beta]).

% debug tallying (['b] [ (['b*], 'a2) ]);;
% result:[{'a2:=[ 'b* ]}]
tally_07_test() ->
  Alpha = tvar(alpha),
  Beta = tvar(beta),
  test_tally(
    [
    {tlist(Beta), Alpha}
  ],
    [{
      #{ alpha => tlist(Beta)},
      #{ alpha => tany() }
    }],
    [beta]
  ).

% see #36
% # debug tallying ([] [(1|2, 'alpha) ( (Int -> Int) & ((1|2) -> (1|2)), 'alpha -> 'beta) ('beta, 1|2)]);;
% [DEBUG:tallying]
% Result:[{'beta:=1--2 | 1--2 & 'a6a6; 'alpha:=1--2 | 1--2 & 'a6a6}]
tally_08_test() ->
  Alpha = tvar(alpha),
  Beta = tvar(beta),
  OneOrTwo = tunion(tint(1), tint(2)),
  OneOrTwoRange = trange(1, 2),
  test_tally(
    [
      {OneOrTwo, Alpha},
      {Beta, OneOrTwo},
      {tinter(tfun1(tint(), tint()), tfun1(OneOrTwo, OneOrTwo)), tfun1(Alpha, Beta)}
    ],
    [{
      #{ alpha => OneOrTwoRange, beta => OneOrTwoRange },
      #{ alpha => OneOrTwoRange, beta => OneOrTwoRange }
    }]).

% Also see #36
% #debug tallying ([] [( ((Int, Int) -> Int) & ((Int, Float) -> Float) & ((Float, Int) -> Float) & ((Float, Float) -> Float), ('alpha, 'beta) -> 'gamma ) (Int \ (1--2), 'alpha) (1, 'beta) (1, 'delta) (2, 'delta) ('delta, Int) ('gamma, 'delta)]);;
% [DEBUG:tallying]
% Result:[{
%  'gamma:=Int;
%  'delta:=Int;
%  'beta:=1 | Int & 'betabeta;
%  'alpha:=*--0 | 3--* | Int & 'alphaalpha
% }]
tally_09_test() ->
    Alpha = tvar(alpha),
    Beta = tvar(beta),
    Gamma = tvar(gamma),
    Delta = tvar(delta),
    One = tint(1),
    Two = tint(2),
    OneOrTwo = tunion(One, Two),
    I = tint(),
    F = tfloat(),
    test_tally(
      [{tinter([tfun2(I, I, I), tfun2(I, F, F), tfun2(F, I, F), tfun2(F, F, F)]), tfun2(Alpha, Beta, Gamma)},
       {tinter(I, tnot(OneOrTwo)), Alpha},
       {One, Beta},
       {One, Delta},
       {Two, Delta},
       {Delta, I},
       {Gamma, Delta}],

      [{
        #{ alpha => tunion(tunion([trange(3, '*')]), tunion([trange('*', 0)])),
          beta => trange(1, 1),
          gamma => I,
          delta => I },
        #{ alpha => tint(),
          beta => tint(),
          gamma => I,
          delta => I }
      }]
    ).

tally_10_test() ->
    V0 = tvar(v0),
    V2 = tvar(v2),
    V3 = tvar(v3),
    V4 = tvar(v4),
    V5 = tvar(v5),
    V6 = tvar(v6),
    V7 = tvar(v7),
    V8 = tvar(v8),
    A = tatom(a),
    B = tatom(b),
    TupleAny = ttuple1(tany()),
    LargeInter = tinter([V0, tnot(tinter([ttuple1(A), TupleAny])), ttuple1(B), TupleAny]),
    test_tally(
      [{tinter([V0, ttuple1(A), TupleAny]), ttuple1(V3)},
       {tunion([tinter([ttuple1(A), TupleAny]), tinter([ttuple1(B), TupleAny])]), ttuple1(V8)},
       {ttuple1(V2), V0},
       {LargeInter, ttuple1(V8)},
       {LargeInter, ttuple1(V7)},
       {LargeInter, ttuple1(V6)},
       {tinter([V0, ttuple1(A), TupleAny]), ttuple1(V5)},
       {A, V2},
       {tinter([V0, ttuple1(A), TupleAny]), ttuple1(V4)}],
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
  A0 = tvar(alpha0), A1 = tvar(alpha1), A2 = tvar(alpha2), A3 = tvar(alpha3), A4 = tvar(alpha4), A5 = tvar(alpha5), A6 = tvar(alpha6),
  test_tally(
    [
      {tfun_full([A1], A2), A0},
      {A4, A2},
      {tint(42), A4},
      {tintersect([A3, tint()]), A4},
      {tintersect([A3, tint()]), A5},
      {tfun_full([tany()], tbool()), tfun_full([A5], A6)},
      {A6, tbool()},
      {A1, A3}
    ],
    [
      {
        #{ alpha2 => tint(42), alpha1 => tnone(), alpha3 => tnone(), alpha6 => tbool(), alpha4 => tint(42) },
        #{ alpha2 => tany(), alpha1 => tany(), alpha3 => tany(), alpha6 => tbool(), alpha4 => tany() }
      },
      {
        #{ alpha0 => tfun_full([tany()], tint(42)), alpha5 => tnone(), alpha2 => tint(42), alpha1 => tnone(), alpha3 => tnone(), alpha6 => tnone(), alpha4 => tnone() },
        #{ alpha0 => tany(), alpha5 => tnone(), alpha2 => tany(), alpha1 => tinter([tany(), tnegate(tint())]), alpha3 => tinter([tany(), tnegate(tint())]), alpha6 => tbool(), alpha4 => tany() }
      }
    ]).


tally_issue_14_test() ->
  V0 = tvar(v0),
  V2 = tvar(v2),
  V3 = tvar(v3),
  V4 = tvar(v4),
  V5 = tvar(v5),
  V6 = tvar(v6),
  V7 = tvar(v7),
  V8 = tvar(v8),
  A = tatom(a),
  B = tatom(b),
  TupleAny = ttuple1(tany()),
  LargeInter = tinter([V0, tnot(tinter([ttuple1(A), TupleAny])), ttuple1(B), TupleAny]),
  test_tally(
    [{tinter([V0, ttuple1(A), TupleAny]), ttuple1(V3)},
      {tunion([tinter([ttuple1(A), TupleAny]), tinter([ttuple1(B), TupleAny])]), ttuple1(V8)},
      {ttuple1(V2), V0},
      {LargeInter, ttuple1(V8)},
      {LargeInter, ttuple1(V7)},
      {LargeInter, ttuple1(V6)},
      {tinter([V0, ttuple1(A), TupleAny]), ttuple1(V5)},
      {A, V2},
      {tinter([V0, ttuple1(A), TupleAny]), ttuple1(V4)}],
    [{#{}, #{}}]).


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
        #{'$0' => ttuple([tatom(a), tatom(tag)])                                          , '$2' => tatom(a),                     '$3' => tatom(a), '$4' => tatom(a) },
        #{'$0' => tunion([ttuple([tatom(a), tatom(tag)]), ttuple([tatom(b), tatom(tag)])]), '$2' => tunion([tatom(a), tatom(b)]), '$3' => tany(),   '$4' => tany() }
      }
    ]).

tally_fun_cons_test() ->
  A1 = tvar(a1),
  A2 = tvar(a2),
  A3 = tvar(a3),
  A4 = tvar(a4),

  test_tally(
    [
      {tempty_list(), A1},
      {tempty_list(), A2},
      {A3, stdtypes:tlist(tint())},
      {tfun2(A4, A4, A4), tfun2(A1, A2, A3)}
    ],
    [{
      #{ },
      #{ }
    }]).

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
    [{
      #{ },
      #{ }
    }]).

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
  test_tally( [ C2 ], solutions(1)),
  % Before tuple simplification, tally(C1) would produce 2 solutions
  % since ('a2, 42) \ ('a1, 42) == (`a2 \ `a1, 42)
  % we get only one solution, same as
  % since ('a1, 42) \ ('a2, 42) == (`a1 \ `a2, 42)
  test_tally( [ C1 ], solutions(1)).


pretty_printing_bug_test() ->
  V0 = tvar(v1),
  V6 = tvar(v2),
  A = tatom(a),
  B = tatom(b),
  test_tally(
    [{
      tinter([V0, tnot(ttuple1(A)), ttuple1(B)]),
      V6
    }],
    [{#{}, #{}}]).

fun_local_own_test_() ->
  {timeout, 15, {"fun_local_02_plus", fun() ->
    ecache:reset_all(),
    {ok, [Cons]} = file:consult("test_files/tally/fun_local_02_plus.config"),

    % to print out cduce command
    % io:format(user, "~s~n", [test_utils:ety_to_cduce_tally(Cons)]),

    test_tally(
      Cons,
      solutions(50)
    ),
    ok
                                         end}}.

% TODO timeout
%recursive_test_() ->
%  {timeout, 15, {"user_07", fun() ->
%    ecache:reset_all(),
%    {ok, [Cons]} = file:consult("test_files/tally/user_07.config"),
%
%    % to print out cduce command
%    % io:format(user, "~s~n", [test_utils:ety_to_cduce_tally(Cons)]),
%
%    test_tally(
%      Cons,
%      solutions(1)
%    ),
%    ok
%                                         end}}.

% =====
% Map Normalization
% =====
maps_norm_opt_1_test() ->
  % #{int() => int()} ⊏ #{a => β}
  L = tmap([tmap_field_opt(tint(), tint())]),
  R = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),

  test_tally([{L, R}],
    [{#{alpha => tint(), beta => tint()},
      #{alpha => tany(), beta => tany()}}
    ]).

maps_norm_opt_2_test() ->
  % #{int() => int(), atom() => atom()}  ≤  #{a => β}
  L = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(tatom(), tatom())
  ]),
  R = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),

  test_tally([{L, R}],
    [{#{alpha => tunion(tint(), tatom()), beta => tunion(tint(), tatom())},
      #{alpha => tany(), beta => tany()}}
    ]).

maps_norm_opt_3_test() ->
  % #{int() => int(), _       => foo}  ≤  #{a => β}
  % #{int() => int(), _\int() => foo}  ≤  #{a => β}
  L = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(tany(), tatom(foo))
  ]),
  R = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),

  test_tally([{L, R}],
    [{#{alpha => tany(), beta => tunion(tint(), tatom(foo))},
      #{alpha => tany(), beta => tany()}}
    ]).

maps_norm_opt_4_test() ->
  % #{a => int()}  ≤  #{int() => β}
  L1 = tmap([tmap_field_opt(tvar(alpha), tint())]),
  R1 = tmap([tmap_field_opt(tint(), tvar(beta))]),
  test_tally([{L1, R1}], solutions(2)),

  % #{int() => β}  ≤  #{a => int()}
  L2 = tmap([tmap_field_opt(tint(), tvar(beta))]),
  R2 = tmap([tmap_field_opt(tvar(alpha), tint())]),

  test_tally([{L2, R2}], solutions(2)).

maps_norm_opt_5_test() ->
  % #{a => int(), _   => atom()}  ≤  #{β => atom() | int()}
  % #{a => int(), _\a => atom()}  ≤  #{β => atom() | int()}
  L = tmap([
    tmap_field_opt(tvar(alpha), tint()),
    tmap_field_opt(tany(), tatom())
  ]),
  R = tmap([
    tmap_field_opt(tvar(beta), tunion(tatom(), tint()))
  ]),

  test_tally([{L, R}], solutions(1)).

maps_norm_opt_6_test() ->
  % #{a => β} ≤ #{atom() => int()}
  L = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),
  R = tmap([tmap_field_opt(tatom(), tint())]),

  test_tally([{L, R}], solutions(3)).


maps_norm_opt_7_test() ->
  % #{a => atom()}  ≤  #{β => any()}
  L = tmap([
    tmap_field_opt(tvar(alpha), tatom())
  ]),
  R = tmap([
    tmap_field_opt(tvar(beta), tany())
  ]),
  test_tally([{L, R}], solutions(1)).

maps_norm_opt_8_test() ->
  % #{}  ≤  #{a => β}
  L = tmap([]),
  R1 = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),
  test_tally([{L, R1}], solutions(1)),

  % #{}  ≤  #{a => β} /\ #{}
  R2 = tintersect([R1, L]),
  test_tally([{L, R2}], solutions(1)).

maps_norm_opt_9_test() ->
  % #{foo => int(), _     => any()}  !≤  #{foo => 1, a     => β}
  % #{foo => int(), _\foo => any()}  !≤  #{foo => 1, a\foo => β}
  L = tmap([
    tmap_field_opt(tatom(foo), tint()),
    tmap_field_opt(tany(), tany())
  ]),
  R = tmap([
    tmap_field_opt(tatom(foo), tint(1)),
    tmap_field_opt(tvar(alpha), tvar(beta))
  ]),
  test_tally([{L, R}], solutions(0)).

maps_norm_opt_10_test() ->
  % #{foo => 1, bar => 2}  ≤  #{a => 1, β => γ}
  L = tmap([
    tmap_field_opt(tatom(foo), tint(1)),
    tmap_field_opt(tatom(bar), tint(2))
  ]),
  R = tmap([
    tmap_field_opt(tvar(alpha), tint(1)),
    tmap_field_opt(tvar(beta), tvar(gamma))
    ]),

  test_tally([{L, R}],solutions(2)).

maps_norm_opt_11_test() ->
  % #{a => β, _   => any()}  ≤  #{γ => δ, _   => any()}
  % #{a => β, _\a => any()}  ≤  #{γ => δ, _\γ => any()}
  L = tmap([
    tmap_field_opt(tvar(alpha), tvar(beta)),
    tmap_field_opt(tany(), tany())
  ]),
  R = tmap([
    tmap_field_opt(tvar(gamma), tvar(delta)),
    tmap_field_opt(tany(), tany())
  ]),
  test_tally([{L, R}], solutions(4)).

maps_norm_opt_12_test() ->
  % #{int() => atom(), atom() => int()}  ≤  #{int() => a, atom() => β, γ              => δ}
  % #{int() => atom(), atom() => int()}  ≤  #{int() => a, atom() => β, γ\int()\atom() => δ}
  L = tmap([
    tmap_field_opt(tint(), tatom()),
    tmap_field_opt(tatom(), tint())
  ]),
  R = tmap([
    tmap_field_opt(tint(), tvar(alpha)),
    tmap_field_opt(tatom(), tvar(beta)),
    tmap_field_opt(tvar(gamma), tvar(delta))
  ]),
  test_tally([{L, R}], solutions(1)).

maps_norm_opt_13_test() ->
  % #{foo => int(), _     => atom()}  ≤  #{a => β, _   => any()} | #{γ => δ, _   => any()}
  % #{foo => int(), _\foo => atom()}  ≤  #{a => β, _\a => any()} | #{γ => δ, _\γ => any()}
  L = tmap([
    tmap_field_opt(tatom(foo), tint()),
    tmap_field_opt(tany(), tatom())
  ]),
  R = tunion(
    tmap([
      tmap_field_opt(tvar(alpha), tvar(beta)),
      tmap_field_opt(tany(), tany())
    ]),
    tmap([
      tmap_field_opt(tvar(gamma), tvar(delta)),
      tmap_field_opt(tany(), tany())
    ])
  ),

  test_tally([{L, R}], solutions(8)).

maps_norm_opt_14_test() ->
  % #{β_0 => β_1} ≤ {a => b}, a ≤ β_0, b ≤ β_1
  L = tmap([
    tmap_field_opt(tvar(beta_0), tvar(beta_1))
  ]),
  R = tmap([
    tmap_field_opt(tatom(a), tatom(b))
  ]),
  Subst = #{beta_0 => tatom(a), beta_1 => tatom(b)},
  test_tally(
    [{L, R}, {tatom(a), tvar(beta_0)}, {tatom(b), tvar(beta_1)}],
    [ {Subst, Subst} ]).

maps_norm_opt_15_test() ->
  % #{a => β_1, 20 => β_3} ≤ {a => b, 20 => 21}
  L = tmap([
    tmap_field_opt(tatom(a), tvar(beta_1)),
    tmap_field_opt(tint(20), tvar(beta_3))
  ]),
  R = tmap([
    tmap_field_opt(tatom(a), tatom(b)),
    tmap_field_opt(tint(20), tint(21))
  ]),
  test_tally([{L, R}], 
    solutions(2) % TODO tuple simplification produces more solutions
    %[ {#{beta_1 => tnone(), beta_3 => tnone()}, #{beta_1 => tatom(b), beta_3 => tint(21)}} ]
  ).

maps_norm_req_1_test() ->
  % #{β_0 := β_1} ≤ {atom() => int()}
  L = tmap([
    tmap_field_req(tvar(beta_0), tvar(beta_1))
  ]),
  R = tmap([
    tmap_field_opt(tatom(), tint())
  ]),
  test_tally([{L, R}, {tatom(a), tvar(beta_0)}, {tint(1), tvar(beta_1)}], [ 
    {
      #{beta_0 => tatom(a), beta_1 => tint(1)}, 
      #{beta_0 => tatom(), beta_1 => tint()}  % cleaned solution is exact
    }]).

maps_norm_req_2_test() ->
  % #{β_0 := β_1, β_2     := β_3} ≤ {a := b, 20   := 21}
  % #{β_0 := β_1, β_2\β_0 := β_3} ≤ {a := b, 20\a := 21}
  L = tmap([
    tmap_field_req(tvar(beta_0), tvar(beta_1)),
    tmap_field_req(tvar(beta_2), tvar(beta_3))
  ]),
  R = tmap([
    tmap_field_req(tatom(a), tatom(b)),
    tmap_field_req(tint(20), tint(21))
  ]),
  test_tally([{L, R}], solutions(10)).


maps_norm_req_3_test() ->
  % #{β_0 := β_1, β_2 := β_3} ≤ {a := b, 20 := 21}, a ≤ β_0, b ≤ β_1, 20 ≤ β_2, 21 ≤ β_3
  L = tmap([
    tmap_field_req(tvar(beta_0), tvar(beta_1)),
    tmap_field_req(tvar(beta_2), tvar(beta_3))
  ]),
  R = tmap([
    tmap_field_req(tatom(a), tatom(b)),
    tmap_field_req(tint(20), tint(21))
  ]),
  test_tally(
    [{L, R}, {tatom(a), tvar(beta_0)}, {tatom(b), tvar(beta_1)}, {tint(20), tvar(beta_2)}, {tint(21), tvar(beta_3)}],
    [{
      #{beta_0 => tatom(a), beta_1 => tatom(b), beta_2 => tint(20), beta_3 => tint(21)}, 
      #{beta_0 => tatom(a), beta_1 => tatom(b), beta_2 => tany(), beta_3 => tint(21)} % cleaned solution is exact
    }]
  ).

maps_norm_req_4_test() ->
  % #{β_0 := β_1} ≤ {a := b, 20 := 21}, a ≤ β_0, b ≤ β_1
  L = tmap([
    tmap_field_req(tvar(beta_0), tvar(beta_1))
  ]),
  R = tmap([
    tmap_field_req(tatom(a), tatom(b)),
    tmap_field_req(tint(20), tint(21))
  ]),
  test_tally(
    [{L, R}, {tatom(a), tvar(beta_0)}, {tatom(b), tvar(beta_1)}],
    solutions(0)
  ).

% symtab usage
% eval_test_() ->
%   {timeout, 150, {"eval_tally_1", fun() ->
%     ecache:reset_all(),
%     {ok, [Cons]} = file:consult("test_files/tally/eval_tally_1_cduce.config"),
%     {ok, [Symtab]} = file:consult("test_files/tally/eval_tally_1.symtab"),
%     Vars = lists:foldl(fun({S, T}, Acc) -> (ty_rec:all_variables(ast_lib:ast_to_erlang_ty(S, Symtab)) ++ ty_rec:all_variables(ast_lib:ast_to_erlang_ty(T, Symtab)) ++ Acc) end, [], Cons),
%     VarOrder = lists:map(fun(V) -> {var, Name} = ast_lib:erlang_ty_var_to_var(V), Name end,lists:sort(lists:flatten(Vars))),

%     % to print out cduce command
%     % io:format(user, "~s~n", [test_utils:ety_to_cduce_tally(Cons, VarOrder)]),

%     test_tally(
%       VarOrder,
%       Cons,
%       Symtab,
%       solutions(1)
%     ),
%     ok
%                                          end}}
% .