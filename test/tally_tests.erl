-module(tally_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("log.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, tfun1/2, trange/2,
                   tunion/1, tunion/2, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0,
                   tint/0, tint/1, ttuple1/1, tinter/1, tinter/2, tlist/1, tempty_list/0,
                   tfloat/0, tfun2/3, tnot/1, tbool/0
                  ]).

-spec test_tally(list({ast:ty(), ast:ty()}), #{ atom() => ast:ty()}) -> ok.
test_tally(ConstrList, ExpectedSubst) ->
    test_tally(ConstrList, ExpectedSubst, []).

-spec test_tally(list({ast:ty(), ast:ty()}), #{ atom() => ast:ty()}, [ast:ty_varname()]) -> ok.
test_tally(_ConstrList, [], _FixedVars) -> ok;
test_tally(ConstrList, AllTests, FixedVars) ->
    Constrs = sets:from_list(
                lists:map(
                  fun ({T, U}) -> {csubty, sets:from_list([ast:loc_auto()]), T, U} end,
                  ConstrList
                 )),

  Res = tally:tally(symtab:empty(), Constrs, sets:from_list(FixedVars)),
  find_subst(AllTests, Res, Res).

find_subst([], [], _) -> ok;
find_subst([{Low, High} | _], [], Sols) ->
  ?LOG_WARN("~nCould not find substitutions among remaining ~p tally solutions for~nExpected lower bound:~n~s~n~nExpected upper bound:~n~s",
            length(Sols),
            pretty:render_subst(Low),
            pretty:render_subst(High)
  ),
  error("test failed because tally returned no substitution that matches low and high bounds");
find_subst([], [X | _Xs], _) -> error({"Too many substitutions:", X});
find_subst(X = [{Low, High} | OtherTests], [Subst | Others], AllTally) ->
  Valid = lists:any(
    fun({{Var, LowerBound}, {Var, UpperBound}}) ->
      begin
        TyOther = maps:get(Var, Subst),
        not (subty:is_subty(none, LowerBound, TyOther) andalso
          subty:is_subty(none, TyOther, UpperBound))
      end
    end, lists:zip(lists:sort(maps:to_list(Low)), lists:sort(maps:to_list(High)))),
  case Valid of
    true -> find_subst(X, Others, AllTally);
    false -> find_subst(OtherTests, AllTally -- [Subst], AllTally -- [Subst])
  end.

tally_01_test() ->
    test_tally([{tvar(alpha), tint()}],
      [{
        #{ alpha => tnone()},
        #{ alpha => tint()}
      }]
    ).

tally_02_test() ->
    test_tally([{tint(), tvar(alpha)}],
      [{
        #{ alpha => tint()},
        #{ alpha => tany()}
      }]
    ).

tally_04_test() ->
  test_tally([
    {ttuple([]), tvar(zero)},
    {tvar(zero), ttuple([])}
  ],
    [{
      #{ zero => ttuple([])},
      #{ zero => ttuple([])}
    }]
  ).

tally_03_test() ->
    Alpha = tvar(alpha),
    Beta = tvar(beta),
    test_tally([
      {Alpha, ttuple1(tany())},
      {ttuple1(Beta), Alpha},
      {tint(), Beta}
    ],
      [{
        #{ alpha => ttuple([tint()]), beta => tint()},
        #{ alpha => ttuple([tany()]), beta => tany()}
      }]
    ).

% TODO lists
%%tally_04_test() ->
%%    Alpha = tvar(alpha),
%%    Beta = tvar(beta),
%%    test_tally_unique([{tlist(Beta), Alpha}],
%%                      #{ alpha => tempty_list() }).

% debug tallying (['b] [ ('b, 'a2) ]);;
% result:[{'a2:='b}]
tally_05_test() ->
    Alpha = tvar(alpha),
    Beta = tvar(beta),
    test_tally(
      [{Beta, Alpha}],
      [{
        #{ alpha => Beta },
        #{ alpha => tany() }
      }],
      [beta]).

% TODO lists
%%% debug tallying (['b] [ (['b*], 'a2) ]);;
%%% result:[{'a2:=[ 'b* ]}]
%%tally_06_test() ->
%%  Alpha = tvar(alpha),
%%  Beta = tvar(beta),
%%  test_tally_unique([{tlist(Beta), Alpha}],
%%    #{ alpha => tunion([tempty_list(), stdtypes:tlist_improper(Beta, tempty_list())]) },
%%    [beta]).

% see #36
% # debug tallying ([] [(1|2, 'alpha) ( (Int -> Int) & ((1|2) -> (1|2)), 'alpha -> 'beta) ('beta, 1|2)]);;
% [DEBUG:tallying]
% Result:[{'beta:=1--2 | 1--2 & 'a6a6; 'alpha:=1--2 | 1--2 & 'a6a6}]
tally_07_test() ->
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

% TODO n-functions
% Also see #36
% #debug tallying ([] [( ((Int, Int) -> Int) & ((Int, Float) -> Float) & ((Float, Int) -> Float) & ((Float, Float) -> Float), ('alpha, 'beta) -> 'gamma ) (Int \ (1--2), 'alpha) (1, 'beta) (1, 'delta) (2, 'delta) ('delta, Int) ('gamma, 'delta)]);;
% [DEBUG:tallying]
% Result:[{'gamma:=Int; 'delta:=Int; 'beta:=1 | Int & 'betabeta;
%         'alpha:=*--0 | 3--* | Int & 'alphaalpha}]
%%tally_08_test() ->
%%    Alpha = tvar(alpha),
%%    Beta = tvar(beta),
%%    Gamma = tvar(gamma),
%%    Delta = tvar(delta),
%%    One = tint(1),
%%    Two = tint(2),
%%    OneOrTwo = tunion(One, Two),
%%    I = tint(),
%%    F = tfloat(),
%%    test_tally_unique(
%%      [{tinter([tfun2(I, I, I), tfun2(I, F, F), tfun2(F, I, F), tfun2(F, F, F)]), tfun2(Alpha, Beta, Gamma)},
%%       {tinter(I, tnot(OneOrTwo)), Alpha},
%%       {One, Beta},
%%       {One, Delta},
%%       {Two, Delta},
%%       {Delta, I},
%%       {Gamma, Delta}],
%%      {
%%        #{ alpha => tunion(tunion([trange(3, '*')]), tunion([trange('*', 0)])),
%%          beta => tunion([trange(1, 1)]),
%%          gamma => I,
%%          delta => I },
%%        #{ alpha => tint(),
%%          beta => tint(),
%%          gamma => I,
%%          delta => I }
%%      }
%%    ).


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
