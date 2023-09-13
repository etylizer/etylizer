-module(dnf_var_ty_function).

-define(P, {dnf_ty_function, ty_variable}).

-behavior(eq).
-export([equal/2, compare/2]).

-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1, normalize/3, substitute/3]).

-export([var/1, function/1, all_variables/1, has_ref/2, transform/2]).

-type dnf_function() :: term().
-type ty_function() :: dnf_function(). % ty_function:type()
-type variable() :: term(). % variable:type()
-type dnf_var_function() :: term().

-spec function(ty_function()) -> dnf_var_function().
function(Tuple) -> gen_bdd:terminal(?P, Tuple).

-spec var(variable()) -> dnf_var_function().
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


is_empty(0) -> true;
is_empty({terminal, Function}) ->
  dnf_ty_function:is_empty(Function);
is_empty({node, _Variable, PositiveEdge, NegativeEdge}) ->
  is_empty(PositiveEdge)
    and is_empty(NegativeEdge).

normalize(Ty, Fixed, M) -> normalize(Ty, [], [], Fixed, M).

normalize(0, _, _, _, _) -> [[]]; % satisfiable
normalize({terminal, Function}, PVar, NVar, Fixed, M) ->
  case ty_ref:is_normalized_memoized(Function, Fixed, M) of
    true ->
      % TODO test case
      error({todo, extract_test_case, memoize_function}); %[[]];
    miss ->
      % memoize only non-variable component t0
      dnf_ty_function:normalize(Function, PVar, NVar, Fixed, sets:union(M, sets:from_list([Function])))
  end;
normalize({node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  constraint_set:merge_and_meet(
    normalize(PositiveEdge, [Variable | PVar], NVar, Fixed, M),
    normalize(NegativeEdge, PVar, [Variable | NVar], Fixed, M)
  ).


substitute(T, M, Memo) -> substitute(T, M, Memo, [], []).

substitute(0, _, _, _, _) -> 0;
substitute({terminal, Function}, Map, Memo, Pos, Neg) ->
  AllPos = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      ty_rec:pi(function, Substitution)
    end, Pos),
  AllNeg = lists:map(
    fun(Var) ->
      Substitution = maps:get(Var, Map, ty_rec:variable(Var)),
      NewNeg = ty_rec:negate(Substitution),
      ty_rec:pi(function, NewNeg)
    end, Neg),

  lists:foldl(fun(Current, All) ->
    intersect(Current, All)
              end, function(dnf_ty_function:substitute(Function, Map, Memo)), AllPos ++ AllNeg);

substitute({node, Variable, PositiveEdge, NegativeEdge}, Map, Memo, P, N) ->

  LBdd = substitute(PositiveEdge, Map, Memo, [Variable | P], N),
  RBdd = substitute(NegativeEdge, Map, Memo, P, [Variable | N]),

  union(LBdd, RBdd).

has_ref(0, _) -> false;
has_ref({terminal, Function}, Ref) ->
  dnf_ty_function:has_ref(Function, Ref);
has_ref({node, _Variable, PositiveEdge, NegativeEdge}, Ref) ->
  has_ref(PositiveEdge, Ref) orelse has_ref(NegativeEdge, Ref).



all_variables(0) -> [];
all_variables({terminal, Function}) -> dnf_ty_function:all_variables(Function);
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
[Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).

transform(0, #{empty := E}) -> E();
transform({terminal, Fun}, Ops) ->
  dnf_ty_function:transform(Fun, Ops);
transform({node, Variable, PositiveEdge, NegativeEdge},
    Ops = #{negate := Negate, var := ToVar, union := Union, intersect := Intersect}) ->
  AstVar = ToVar(Variable),
  Union([
    Intersect([AstVar, transform(PositiveEdge, Ops)]),
    Intersect([Negate(AstVar), transform(NegativeEdge, Ops)])
  ]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  %   any arrow
  TIa = ty_rec:empty(),
  TIb = ty_rec:empty(),
  Ty_F1 = ty_rec:function(dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(TIa, TIb)))),

  %   any arrow 2
  Ty_F2 = ty_rec:function(),

  true = ty_rec:is_subtype(Ty_F1, Ty_F2),
  true = ty_rec:is_subtype(Ty_F2, Ty_F1),
%%  io:format(user, "~p~n", [Bdd]),

  ok.

-endif.
