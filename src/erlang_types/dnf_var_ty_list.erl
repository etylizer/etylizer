-module(dnf_var_ty_list).

-define(P, {dnf_ty_list, ty_variable}).


-export([equal/2, compare/2]).


-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/3, substitute/4]).

-export([var/1, list/1, all_variables/1, has_ref/2, transform/2]).

list(List) -> gen_bdd:terminal(?P, List).

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

is_any(B) -> gen_bdd:is_any(?P, B).
is_empty(TyBDD) -> gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_list:is_empty(T).

% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

normalize(Ty, Fixed, M) ->
  New = normalize_new(Ty, Fixed, M),
  New = normalize(Ty, [], [], Fixed, M).

normalize_new(Ty, Fixed, M) ->
  gen_bdd:dnf(?P, Ty, {fun(Pos, Neg, DnfTyList) -> normalize_coclause(Pos, Neg, DnfTyList, Fixed, M) end, fun constraint_set:meet/2}).

normalize_coclause(Pos, Neg, {terminal, 0}, Fixed, M) -> [[]];
normalize_coclause(PVar, NVar, List, Fixed, M) ->
  case ty_ref:is_normalized_memoized(List, Fixed, M) of
    true ->
      % TODO test case
      error({todo, extract_test_case, memoize_function}); %[[]];
    miss ->
      % memoize only non-variable component t0
      dnf_ty_list:normalize(List, PVar, NVar, Fixed, sets:union(M, sets:from_list([List])))
  end
.

normalize({terminal, {terminal, 0}}, _, _, _, _) -> [[]]; % satisfiable
normalize({terminal, List}, PVar, NVar, Fixed, M) ->
  case ty_ref:is_normalized_memoized(List, Fixed, M) of
    true ->
      % TODO test case
      error({todo, extract_test_case, memoize_function}); %[[]];
    miss ->
      % memoize only non-variable component t0
      dnf_ty_list:normalize(List, PVar, NVar, Fixed, sets:union(M, sets:from_list([List])))
  end;
normalize({node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  constraint_set:merge_and_meet(
    normalize(PositiveEdge, [Variable | PVar], NVar, Fixed, M),
    normalize(NegativeEdge, PVar, [Variable | NVar], Fixed, M)
  ).

substitute(MkTy, T, M, Memo) ->
  gen_bdd:substitute(?P, MkTy, T, M, Memo).

has_ref({terminal, {terminal, 0}}, _) -> false;
has_ref({terminal, List}, Ref) ->
  dnf_ty_list:has_ref(List, Ref);
has_ref({node, _Variable, PositiveEdge, NegativeEdge}, Ref) ->
  has_ref(PositiveEdge, Ref) orelse has_ref(NegativeEdge, Ref).

all_variables({terminal, {terminal, 0}}) -> [];
all_variables({terminal, List}) -> dnf_ty_list:all_variables(List);
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
  [Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).

transform({terminal, {terminal, 0}}, #{empty := E}) -> E();
transform({terminal, List}, Ops) ->
  dnf_ty_list:transform(List, Ops);
transform({node, Variable, PositiveEdge, NegativeEdge},
    Ops = #{negate := Negate, var := ToVar, union := Union, intersect := Intersect}) ->
  AstVar = ToVar(Variable),
  Union([
    Intersect([AstVar, transform(PositiveEdge, Ops)]),
    Intersect([Negate(AstVar), transform(NegativeEdge, Ops)])
  ]).
