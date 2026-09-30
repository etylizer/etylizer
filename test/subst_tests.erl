-module(subst_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tunion/1, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0]).
-import(test_utils, [is_subtype/2, is_equiv/2]).

ast_to_erlang_ty(Ty) ->
  ty_parser:parse(Ty).

ast_to_erlang_ty_var({var, Name}) ->
  ty_variable:new_with_name(Name).

all_variables(Ty) ->
  sets:to_list(ty:all_variables(Ty)).

test_subst(Name, Subst, Type, TypeExpected) ->
  {Name, fun() ->
    global_state:with_new_state(fun() ->
      SubstT = maps:from_list([{ast_to_erlang_ty_var(Var), ast_to_erlang_ty(Ty)} || {Var, Ty} <- maps:to_list(Subst)]),
      TypeT = ast_to_erlang_ty(Type),
      TypeExpectedT = ast_to_erlang_ty(TypeExpected),
      New = ty:substitute(TypeT, SubstT),
      true = ty:is_equivalent(New, TypeExpectedT)
                                end) 
         end
  }.

eq_list(L1, L2) ->
  S1 = sets:from_list(L1),
  S2 = sets:from_list(L2),
  sets:is_subset(S1, S2) andalso sets:is_subset(S2, S1).

all_variables_fun_test() ->
  global_state:with_new_state(fun() ->
    T = tfun_full([tvar('$0'), tvar('$1')], tvar('$2')),
    Ty = ast_to_erlang_ty(T),
    true = eq_list([ast_to_erlang_ty_var(tvar(V)) || V <- ['$0', '$1', '$2']], all_variables(Ty))
  end).

all_variables_tuple_test() ->
  global_state:with_new_state(fun() ->
    T = ttuple([tvar('$0'), tvar('$1'), tvar('$2')]),
    Ty = ast_to_erlang_ty(T),
    true = eq_list([ast_to_erlang_ty_var(tvar(V)) || V <- ['$0', '$1', '$2']], all_variables(Ty))
  end).

all_variables_test() ->
  global_state:with_new_state(fun() ->
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
    true = eq_list([ast_to_erlang_ty_var(tvar(V)) || V <- ['$1', '$2', '$3', '$4', '$5', '$6', '$7', '$8', '$9', '$10', '$11', '$12']], all_variables(Ty)),
    ok
  end).

simple_subst_test() ->
  global_state:with_new_state(fun() ->
    All = [tatom(), trange_any(), stdtypes:tspecial_any(), stdtypes:tlist_any(), stdtypes:tfun_any(), stdtypes:ttuple_any()],
    Ty = ast_to_erlang_ty(tvar('a')),
    [
      begin
        TargetTy = ast_to_erlang_ty(Target),
        true = ty:is_equivalent(TargetTy, ty:substitute(Ty, #{ast_to_erlang_ty_var(tvar('a')) => TargetTy}))
      end
      || Target <- All],
    ok
  end).

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
    global_state:with_new_state(fun() ->
        E = stdtypes:tnone(),

        % a is in covariant position
        A = stdtypes:tvar('a'),
        B = stdtypes:tvar('b'),
        E = subst:clean(A, sets:new(), symtab:empty()),

        % intersection: covariant
        E = subst:clean(stdtypes:tinter(A, B), sets:new(), symtab:empty()),

        % union: covariant
        E = subst:clean(stdtypes:tunion(A, B), sets:new(), symtab:empty()),

        % negation: flip
        E = subst:clean(stdtypes:tnegate(A), sets:new(), symtab:empty()),

        % function type flips argument variable position
        Arr = stdtypes:tfun1(stdtypes:tany(), stdtypes:tnone()),
        Arr = subst:clean(stdtypes:tfun1(A, B), sets:new(), symtab:empty()),

        % function double flip
        Arr2 = stdtypes:tfun1(stdtypes:tfun1(stdtypes:tnone(), stdtypes:tany()), stdtypes:tnone()),
        Arr2 = subst:clean(stdtypes:tfun1(stdtypes:tfun1(A, B), stdtypes:tnone()), sets:new(), symtab:empty())
    end).

clean_negate_var_test() ->
    global_state:with_new_state(fun() ->
        A = stdtypes:tvar('a'),
        E = stdtypes:tnone(),

        % negation is covariant position
        E = subst:clean(stdtypes:tnegate(A), sets:new(), symtab:empty()),
        % test nnf
        E = subst:clean(stdtypes:tnegate(stdtypes:tunion(A, stdtypes:tnegate(stdtypes:tatom()))), sets:new(), symtab:empty())
    end).

% TODO: better unparsing to ensure that (int, Bottom) = Bottom
% clean_tuples_test() ->
%     global_state:with_new_state(fun() ->
%         A = stdtypes:tvar('a'),
%         E = stdtypes:tnone(),
%         T = stdtypes:tany(),
%
%         % clean((int, a)) = (int, Bottom) = Bottom
%         Ty1 = subst:clean(stdtypes:ttuple2(stdtypes:tint(), A), sets:new()),
%         io:format(user,"~n~p vs ~p~n", [Ty1, E]),
%         Ty1 = E,
%
%         % clean(!(int, a)) = !(int, Top)
%         Ty2 = subst:clean(stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), A)), sets:new()),
%         Ty2 = stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), T)),
%
%         % clean(!(int, !a)) = !(int, !Empty) = !(int, Top)
%         Ty3 = subst:clean(stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), stdtypes:tnegate(A))), sets:new()),
%         Ty3 = stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), T)),
%
%         % clean(!(int, !(int, a))) = !(int, !(int, Bottom)) = !(int, Top) = !(int, Top)
%         Ty4 = subst:clean(stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), A)))), sets:new()),
%         Ty4 = stdtypes:tnegate(stdtypes:ttuple2(stdtypes:tint(), T))
%
%     end).
%

clean(Cs) -> clean(Cs, []).
clean(Cs, Fixed) ->
    global_state:with_new_state(fun() -> subst:clean_cons(Cs, sets:from_list(Fixed), symtab:empty()) end).

clean_cons_vars_test() ->
    {A, Atom, Int} = {tvar(a), tatom(), stdtypes:tint()},
    % never nested and bounded on one side only, what is left is trivially true
    [] = clean([{A, Atom}]),
    [] = clean([{Atom, A}]),
    % never nested and bounded on both sides, a is eliminated by transitivity
    [{Atom, Int}] = clean([{Atom, A}, {A, Int}]),
    % nested covariantly, the union of the lower bounds is the only choice
    [{{tuple, [Atom]}, Int}] = clean([{Atom, A}, {ttuple([A]), Int}]),
    % nested contravariantly, the intersection of the upper bounds
    [{Int, {tuple, [Atom]}}] = clean([{A, Atom}, {Int, ttuple([A])}]),
    % several lower bounds, a becomes their union, and each bound is then a
    % member of the union it is compared with, which is trivially true as well
    [{{tuple, [{union, U}]}, Int}] = clean([{Atom, A}, {Int, A}, {ttuple([A]), Int}]),
    [Atom, Int] = lists:sort(U),
    % nested at both polarities, no best value, a is left alone
    In = [{ttuple([A]), Int}, {Atom, ttuple([A])}],
    In = clean(In),
    % fixed variables are never cleaned
    [{A, Atom}] = clean([{A, Atom}], [a]).

clean_cons_dependent_body_test() ->
    {A, B, Atom, Int} = {tvar(a), tvar(b), tatom(), stdtypes:tint()},
    % a self-reference can never be applied, so nothing is cleaned at all
    In = [{ttuple([A]), A}, {A, Int}],
    In = clean(In),
    % b's body is a, and a is substituted in round 1, so b waits; round 2 sees
    % b's lower bound as none() and cleans b as well
    [{{tuple, [{predef, none}]}, Int}] = clean([{A, Atom}, {A, B}, {ttuple([B]), Int}]),
    % a mutual pair, dropping one body frees the other, so b still goes
    [] = clean([{A, B}, {B, A}]).
