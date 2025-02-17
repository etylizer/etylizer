-module(subst_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tunion/1, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0]).
-import(test_utils, [is_subtype/2, is_equiv/2]).

ast_to_erlang_ty(Ty) ->
  ast_lib:ast_to_erlang_ty(Ty, symtab:empty()).

test_subst(Name, Subst, Type, TypeExpected) ->
  {Name, fun() ->
    test_utils:reset_ets(),
    SubstT = maps:from_list([{ast_lib:ast_to_erlang_ty_var(Var), ast_to_erlang_ty(Ty)} || {Var, Ty} <- maps:to_list(Subst)]),
    TypeT = ast_to_erlang_ty(Type),
    TypeExpectedT = ast_to_erlang_ty(TypeExpected),
    New = ty_rec:substitute(TypeT, SubstT),
    true = ty_rec:is_equivalent(New, TypeExpectedT)
                end
  }.

eq_list(L1, L2) ->
  S1 = sets:from_list(L1, [{version, 2}]),
  S2 = sets:from_list(L2, [{version, 2}]),
  sets:is_subset(S1, S2) andalso sets:is_subset(S2, S1).

all_variables_fun_test() ->
  test_utils:reset_ets(),
  T = tfun_full([tvar('$0'), tvar('$1')], tvar('$2')),
  Ty = ast_to_erlang_ty(T),
  true = eq_list([ast_lib:ast_to_erlang_ty_var(tvar(V)) || V <- ['$0', '$1', '$2']], ty_rec:all_variables(Ty)),
  ok.

all_variables_tuple_test() ->
  test_utils:reset_ets(),
  T = ttuple([tvar('$0'), tvar('$1'), tvar('$2')]),
  Ty = ast_to_erlang_ty(T),
  true = eq_list([ast_lib:ast_to_erlang_ty_var(tvar(V)) || V <- ['$0', '$1', '$2']], ty_rec:all_variables(Ty)),
  ok.

all_variables_test() ->
  test_utils:reset_ets(),
  T = tunion([
    tintersect([tvar('$1'), tatom()]),
    tintersect([tvar('$2'), trange_any()]),
    tintersect([tvar('$3'), stdtypes:tempty_list()]),
    tintersect([tvar('$4'), stdtypes:tlist(tvar('$5'))]),
    tintersect([tvar('$5'), ttuple([])]),
    tintersect([tvar('$6'), ttuple([tvar('$7')])]),
    tintersect([tvar('$8'), tfun_full([], tvar('$9'))]),
    tintersect([tvar('$10'), tfun_full([tvar('$11')], tvar('$12'))])
  ]),
  Ty = ast_to_erlang_ty(T),
  true = eq_list([ast_lib:ast_to_erlang_ty_var(tvar(V)) || V <- ['$1', '$2', '$3', '$4', '$5', '$6', '$7', '$8', '$9', '$10', '$11', '$12']], ty_rec:all_variables(Ty)),
  ok.

simple_subst_test() ->
  test_utils:reset_ets(),
  All = [tatom(), trange_any(), stdtypes:tspecial_any(), stdtypes:tlist_any(), stdtypes:tfun_any(), stdtypes:ttuple_any()],
  Ty = ast_to_erlang_ty(tvar('a')),
  [
    begin
      TargetTy = ast_to_erlang_ty(Target),
      true = ty_rec:is_equivalent(TargetTy, ty_rec:substitute(Ty, #{ast_lib:ast_to_erlang_ty_var(tvar('a')) => TargetTy}))
    end
    || Target <- All],
  ok.

tuple_test_() ->
  [
    test_subst(Name, Subst, Ty, TyExpected) || {Name, Subst, Ty, TyExpected} <-
    [
      % a => {1,1}
      % a & {1} => Empty
      {
        "var other category",
        #{tvar('a') => ttuple([tany(), tany()])},
        tintersect([tvar('a'), ttuple([tany()])]),
        tnone()
      },
      % a => {1,1}
      % a & {1,atom} => {1,atom} & (1,1) => {1,atom}
      {
        "var same category",
        #{tvar('a') => ttuple([tany(), tany()])},
        tintersect([tvar('a'), ttuple([tany(), tatom()])]),
        ttuple([tany(), tatom()])
      },
      % a => {1,1}
      % a U {1,atom} => {1,atom} U (1,1) => {1,1}
      {
        "var same category II",
        #{tvar('a') => ttuple([tany(), tany()])},
        tunion([tvar('a'), ttuple([tany(), tatom()])]),
        ttuple([tany(), tany()])
      }
    ]
  ].


tuple_change_category_test_() ->
  [
    test_subst(Name, Subst, Ty, TyExpected) || {Name, Subst, Ty, TyExpected} <-
    [
      % a => {1}
      % a & {} => Empty
      {
        "eliminating a different category",
        #{tvar('a') => ttuple([tany()])},
        tintersect([tvar('a'), ttuple([])]),
        tnone()
      },
      % a => {1}
      % (a & tuple) U (a &{}) => {1}
      {
        "transform a different category",
        #{tvar('a') => ttuple([tany()])},
        tunion([tintersect([tvar('a'), stdtypes:ttuple_any()]), tintersect([tvar('a'), ttuple([])])]),
        ttuple([tany()])
      }
    ]
  ].

clean_test() ->
    ecache:reset_all(),

    E = stdtypes:tnone(),

    % a is in covariant position
    A = stdtypes:tvar('a'),
    B = stdtypes:tvar('b'),
    E = subst:clean(A, sets:new([{version, 2}])),

    % intersection: covariant
    E = subst:clean(stdtypes:tinter(A, B), sets:new([{version, 2}])),

    % union: covariant
    E = subst:clean(stdtypes:tunion(A, B), sets:new([{version, 2}])),

    % negation: flip
    E = subst:clean(stdtypes:tnegate(A), sets:new([{version, 2}])),

    % function type flips argument variable position
    Arr = stdtypes:tfun1(stdtypes:tany(), stdtypes:tnone()),
    Arr = subst:clean(stdtypes:tfun1(A, B), sets:new([{version, 2}])),

    % function double flip
    Arr2 = stdtypes:tfun1(stdtypes:tfun1(stdtypes:tnone(), stdtypes:tany()), stdtypes:tnone()),
    Arr2 = subst:clean(stdtypes:tfun1(stdtypes:tfun1(A, B), stdtypes:tnone()), sets:new([{version, 2}])),

    ok.

clean_negate_var_test() ->
    ecache:reset_all(),
    A = stdtypes:tvar('a'),
    E = stdtypes:tnone(),

    % negation is covariant position
    E = subst:clean(stdtypes:tnegate(A), sets:new([{version, 2}])),
    % test nnf
    E = subst:clean(stdtypes:tnegate(stdtypes:tunion(A, stdtypes:tnegate(stdtypes:tatom()))), sets:new([{version, 2}])).

clean_tuples_test() ->
    ecache:reset_all(),

    A = stdtypes:tvar('a'),
    E = stdtypes:tnone(),
    T = stdtypes:tany(),

    % clean((int, a)) = (int, Bottom) = Bottom
    Ty1 = subst:clean(stdtypes:ttuple2(stdtypes:tint(), A), sets:new([{version, 2}])),
    Ty1 = E,

    % clean(!(int, a)) = !(int, Top)
    Ty2 = subst:clean(stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), A)), sets:new([{version, 2}])),
    Ty2 = stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), T)),

    % clean(!(int, !a)) = !(int, !Empty) = !(int, Top)
    Ty3 = subst:clean(stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), stdtypes:tnegate(A))), sets:new([{version, 2}])),
    Ty3 = stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), T)),

    % clean(!(int, !(int, a))) = !(int, !(int, Bottom)) = !(int, Top) = !(int, Top)
    Ty4 = subst:clean(stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), A)))), sets:new([{version, 2}])),
    Ty4 = stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), T)),

    ok.
