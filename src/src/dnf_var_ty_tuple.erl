-module(dnf_var_ty_tuple).
-vsn({2,0,0}).

-define(P, {dnf_ty_tuple, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

%%-behavior(type). %TODO parameterize over size too
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/2, is_any/1, normalize/4, substitute/4]).

-export([var/1, tuple/1, all_variables/1, has_ref/2, transform/2]).

-type dnf_tuple() :: term().
-type ty_tuple() :: dnf_tuple(). % ty_tuple:type()
-type variable() :: term(). % variable:type()
-type dnf_var_tuple() :: term().

-spec tuple(ty_tuple()) -> dnf_var_tuple().
tuple(Tuple) -> gen_bdd:terminal(?P, Tuple).

-spec var(variable()) -> dnf_var_tuple().
var(Var) -> gen_bdd:element(?P, Var).

% ==
% type interface
% ==
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).

union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).

eval(B) -> gen_bdd:eval(?P, B).
is_any(B) -> gen_bdd:is_any(?P, B).

% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

is_empty(_, 0) -> true;
is_empty(Size, {terminal, Tuple}) ->
  dnf_ty_tuple:is_empty(Size, Tuple);
is_empty(Size, {node, _Variable, PositiveEdge, NegativeEdge}) ->
  is_empty(Size, PositiveEdge)
    and is_empty(Size, NegativeEdge).

normalize(Size, Ty, Fixed, M) -> normalize(Size, Ty, [], [], Fixed, M).

normalize(_, 0, _, _, _, _) -> [[]]; % satisfiable
normalize(Size, {terminal, Tuple}, PVar, NVar, Fixed, M) ->
  case ty_ref:is_normalized_memoized(Tuple, Fixed, M) of
    true ->
      % TODO test case
      error({todo, extract_test_case, memoize_function}); %[[]];
    miss ->
      % memoize only non-variable component t0
      dnf_ty_tuple:normalize(Size, Tuple, PVar, NVar, Fixed, sets:union(M, sets:from_list([Tuple])))
  end;
normalize(Size, {node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  R = constraint_set:merge_and_meet(
    N1 = normalize(Size, PositiveEdge, [Variable | PVar], NVar, Fixed, M),
    N2 = normalize(Size, NegativeEdge, PVar, [Variable | NVar], Fixed, M)
  ),
  io:format(user, "Normalize (~p) ~p with ~p to ~n~p~n", [Size, N1, N2, R]),
  R.

substitute(Size, T, M, Memo) -> substitute(Size, T, M, Memo, [], []).

substitute(_, 0, _, _, _, _) -> {empty(), #{}};
substitute(Size, {terminal, Tuple}, Map, Memo, Pos, Neg) ->
  AllPos = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      ty_rec:pi(tuple, Substitution)
    end, Pos),
  AllNeg = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      NewNeg = ty_rec:negate(Substitution),
      ty_rec:pi(tuple, NewNeg)
    end, Neg),

  Base = case Size of
           default ->
             {tuple(dnf_ty_tuple:substitute(Tuple, Map, Memo)), #{}};
           _ ->
             {empty(), #{Size => tuple(dnf_ty_tuple:substitute(Tuple, Map, Memo))}}
         end,
  lists:foldl(fun({CurrentDefault, CurrentTuple}, {AllDefault, AllTuple}) ->
    {intersect(CurrentDefault, AllDefault), mingle(CurrentDefault, AllDefault, CurrentTuple, AllTuple, fun intersect/2)}
              end, Base, AllPos ++ AllNeg);

substitute(Size, {node, Variable, PositiveEdge, NegativeEdge}, Map, Memo, P, N) ->
  {LeftDefault, LeftOthers} = substitute(Size, PositiveEdge, Map, Memo, [Variable | P], N),
  {RightDefault, RightOthers} = substitute(Size, NegativeEdge, Map, Memo, P, [Variable | N]),

  {union(LeftDefault, RightDefault), mingle(LeftDefault, RightDefault, LeftOthers, RightOthers, fun union/2)}.

has_ref(0, _) -> false;
has_ref({terminal, Tuple}, Ref) ->
  dnf_ty_tuple:has_ref(Tuple, Ref);
has_ref({node, _Variable, PositiveEdge, NegativeEdge}, Ref) ->
  has_ref(PositiveEdge, Ref) orelse has_ref(NegativeEdge, Ref).

all_variables({Default, Others}) when is_map(Others) ->
  all_variables(Default) ++ lists:map(fun({_K,V}) -> all_variables(V) end, maps:to_list(Others));
all_variables(0) -> [];
all_variables({terminal, Tuple}) -> dnf_ty_tuple:all_variables(Tuple);
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
  [Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).


mingle(LeftDefault, RightDefault, AllLeft, AllRight, Op) ->
  AllKeys = maps:keys(AllLeft) ++ maps:keys(AllRight),
  % LeftDefault + Right (left not assigned)  Left + RightDefault (right not assigned) Left + Right (both)
  maps:from_list(lists:map(fun(Key) -> {Key, Op(maps:get(Key, AllLeft, LeftDefault), maps:get(Key, AllRight, RightDefault))} end, AllKeys)).


transform(0, #{empty := E}) -> E();
transform({terminal, Tuple}, Ops) ->
  dnf_ty_tuple:transform(Tuple, Ops);
transform({node, Variable, PositiveEdge, NegativeEdge},
    Ops = #{negate := Negate, var := ToVar, union := Union, intersect := Intersect}) ->
  AstVar = ToVar(Variable),
  Union([
    Intersect([AstVar, transform(PositiveEdge, Ops)]),
    Intersect([Negate(AstVar), transform(NegativeEdge, Ops)])
  ]).

%%-ifdef(TEST).
%%-include_lib("eunit/include/eunit.hrl").
%%
%%usage_test() ->
%%  %   a1 ^ (int, int)
%%  TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
%%  TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
%%  Ty_Tuple = ty_tuple:tuple(TIa, TIb),
%%
%%  VarA = ty_variable:new("a1"),
%%
%%  Dnf_Ty_Tuple = dnf_ty_tuple:tuple(Ty_Tuple),
%%
%%  BVar1 = dnf_var_ty_tuple:var(VarA),
%%  BTupleA = dnf_var_ty_tuple:tuple(Dnf_Ty_Tuple),
%%
%%  Bdd = dnf_var_ty_tuple:intersect(BVar1, BTupleA),
%%
%%  false = dnf_var_int:is_empty(Bdd),
%%%%  io:format(user, "~p~n", [Bdd]),
%%
%%  ok.
%%
%%-endif.
