-module(dnf_ty_list).

-define(P, {bdd_bool, ty_list}).
-define(F(Z), fun() -> Z end).


-export([equal/2, compare/2]).


-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/1, is_any/1, normalize/5, substitute/3]).

-export([list/1, all_variables/1, has_ref/2, transform/2]).

list(TyList) -> gen_bdd:element(?P, TyList).

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

is_empty(TyBDD) -> is_empty(
  TyBDD,
  ty_rec:any(),
  ty_rec:any(),
  _NegatedLists = []
).

is_empty(0, _, _, _) -> true;
is_empty({terminal, 1}, S1, S2, N) ->
  phi(S1, S2, N);
is_empty({node, TyList, L_BDD, R_BDD}, BigS1, BigS2, Negated) ->
  S1 = ty_list:pi1(TyList),
  S2 = ty_list:pi2(TyList),

  is_empty(L_BDD, ty_rec:intersect(S1, BigS1), ty_rec:intersect(S2, BigS2), Negated)
  andalso
    is_empty(R_BDD, BigS1, BigS2, [TyList | Negated]).

phi(S1, S2, []) ->
  ty_rec:is_empty(S1)
    orelse
    ty_rec:is_empty(S2);
phi(S1, S2, [Ty | N]) ->
  ty_rec:is_empty(S1)
    orelse ty_rec:is_empty(S2)
    orelse (
      begin
        T1 = ty_list:pi1(Ty),
        T2 = ty_list:pi2(Ty),
        phi(ty_rec:diff(S1, T1), S2, N)
          andalso
          phi(S1, ty_rec:diff(S2, T2), N)
      end
  ).

normalize(TyList, [], [], Fixed, M) ->
  normalize_no_vars(TyList, ty_rec:any(), ty_rec:any(), _NegatedLists = [], Fixed, M);
normalize(DnfTyList, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:list(dnf_var_ty_list:list(DnfTyList)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:list(dnf_var_ty_list:var(Var)) end, M).

normalize_no_vars(0, _, _, _, _Fixed, _) -> [[]]; % empty
normalize_no_vars({terminal, 1}, S1, S2, N, Fixed, M) ->
  phi_norm(S1, S2, N, Fixed, M);
normalize_no_vars({node, TyList, L_BDD, R_BDD}, BigS1, BigS2, Negated, Fixed, M) ->
  S1 = ty_list:pi1(TyList),
  S2 = ty_list:pi2(TyList),

  X1 = ?F(normalize_no_vars(L_BDD, ty_rec:intersect(S1, BigS1), ty_rec:intersect(S2, BigS2), Negated, Fixed, M)),
  X2 = ?F(normalize_no_vars(R_BDD, BigS1, BigS2, [TyList | Negated], Fixed, M)),
  constraint_set:meet(X1, X2).

phi_norm(S1, S2, [], Fixed, M) ->
  T1 = ?F(ty_rec:normalize(S1, Fixed, M)),
  T2 = ?F(ty_rec:normalize(S2, Fixed, M)),
  constraint_set:join(T1, T2);
phi_norm(S1, S2, [Ty | N], Fixed, M) ->
  T1 = ?F(ty_rec:normalize(S1, Fixed, M)),
  T2 = ?F(ty_rec:normalize(S2, Fixed, M)),

  T3 =
    ?F(begin
      TT1 = ty_list:pi1(Ty),
      TT2 = ty_list:pi2(Ty),
      X1 = ?F(phi_norm(ty_rec:diff(S1, TT1), S2, N, Fixed, M)),
      X2 = ?F(phi_norm(S1, ty_rec:diff(S2, TT2), N, Fixed, M)),
      constraint_set:meet(X1, X2)
    end),

  constraint_set:join(T1, ?F(constraint_set:join(T2, T3))).


substitute(0, _, _) -> 0;
substitute({terminal, 1}, _, _) ->
  {terminal, 1};
substitute({node, TyList, L_BDD, R_BDD}, Map, Memo) ->
  S1 = ty_list:pi1(TyList),
  S2 = ty_list:pi2(TyList),

  NewS1 = ty_rec:substitute(S1, Map, Memo),
  NewS2 = ty_rec:substitute(S2, Map, Memo),

  NewTyList = ty_list:list(NewS1, NewS2),

  union(
    intersect(list(NewTyList), L_BDD),
    intersect(negate(list(NewTyList)), R_BDD)
    ).

has_ref(0, _) -> false;
has_ref({terminal, _}, _) -> false;
has_ref({node, List, PositiveEdge, NegativeEdge}, Ref) ->
  ty_list:has_ref(List, Ref)
    orelse
    has_ref(PositiveEdge, Ref)
    orelse
    has_ref(NegativeEdge, Ref).

all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, List, PositiveEdge, NegativeEdge}) ->
  ty_rec:all_variables(ty_list:pi1(List))
  ++ ty_rec:all_variables(ty_list:pi2(List))
    ++ all_variables(PositiveEdge)
    ++ all_variables(NegativeEdge).

transform(0, #{empty := F}) -> F();
transform({terminal, 1}, #{any_list := F}) -> F();
transform({node, List, PositiveEdge, NegativeEdge}, Ops = #{negate := N, union := U, intersect := I} ) ->
  NF = ty_list:transform(List, Ops),

  U([
    I([NF, transform(PositiveEdge, Ops)]),
    I([N(NF), transform(NegativeEdge, Ops)])
  ]).

