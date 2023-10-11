-module(dnf_ty_list).

-define(P, {bdd_bool, ty_list}).
-define(F(Z), fun() -> Z end).


-export([equal/2, compare/2]).


-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/5, substitute/3]).

-export([list/1, all_variables/1, has_ref/2, transform/2]).

list(TyList) -> gen_bdd:element(?P, TyList).

% ==
% type interface
% ==
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).

substitute(TyBDD, Map, Memo) -> gen_bdd:substitute(?P, TyBDD, Map, Memo).

union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).

is_any(B) -> gen_bdd:is_any(?P, B).

% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

is_empty(TyBDD) ->
  gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).

is_empty_coclause(_Pos, _Neg, 0) -> true;
is_empty_coclause(Pos, Neg, 1) ->
  Big = ty_list:big_intersect(Pos),
  S1 = ty_list:pi1(Big),
  S2 = ty_list:pi2(Big),
  ty_rec:is_empty(S1) orelse
    ty_rec:is_empty(S2) orelse
    phi(S1, S2, Neg).

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
  gen_bdd:dnf(?P, TyList, {
    fun(Pos, Neg, DnfTyList) ->
      normalize_coclause(Pos, Neg, DnfTyList, Fixed, M)
                                 end,
    fun constraint_set:meet/2
  });
normalize(DnfTyList, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:list(dnf_var_ty_list:list(DnfTyList)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:list(dnf_var_ty_list:var(Var)) end, M).


normalize_coclause(_Pos, _Neg, 0, _Fixed, _M) -> [[]];
normalize_coclause(Pos, Neg, 1, Fixed, M) ->
  Big = ty_list:big_intersect(Pos),
  S1 = ty_list:pi1(Big),
  S2 = ty_list:pi2(Big),
  phi_norm(S1, S2, Neg, Fixed, M).

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

subst_coclause(_P, _N, 0, _Map, _Memo) -> empty();
subst_coclause(P, N, 1, Map, Memo) ->
  PosL = lists:map(fun(L) -> list(ty_list:substitute(L, Map, Memo)) end, P),
  NegL = lists:map(fun(L) -> negate(list(ty_list:substitute(L, Map, Memo))) end, N),
  Res = lists:foldl(fun(E,Ac) -> intersect(E, Ac) end, any(), PosL ++ NegL),
  Res.

has_ref(TyBDD, Ref) ->
  gen_bdd:dnf(?P, TyBDD, {
    fun(P,N,T) -> has_ref(P,N,T,Ref) end,
    fun(F1, F2) -> F1() orelse F2() end
  }).

has_ref(_P, _N, 0, _) -> false;
has_ref(P, N, 1, Ref) ->
  Fun = fun(F) -> ty_list:has_ref(F, Ref) end,
  lists:any(Fun, P) orelse lists:any(Fun, N).

all_variables(TyBDD) ->
  gen_bdd:dnf(?P, TyBDD, {
    fun all_vars_coclause/3,
    fun(F1, F2) -> lists:usort(F1() ++ F2()) end
  }).

all_vars_coclause(_,_,0) -> [];
all_vars_coclause(P,N,1) ->
  lists:foldl(fun(L, Acc) -> Acc ++ ty_list:all_variables(L) end, [], P) ++
  lists:foldl(fun(L, Acc) -> Acc ++ ty_list:all_variables(L) end, [], N) .

transform(TyBDD, OpMap = #{union := U}) ->
  gen_bdd:dnf(?P, TyBDD, {
    fun(P,N,T) -> transform_coclause(P,N,T,OpMap) end,
    fun(F1, F2) -> U([F1(), F2()]) end
  }).

transform_coclause(_,_,0,#{empty := E}) -> E();
transform_coclause(Pos,Neg,1, Ops = #{negate := N, intersect := I} ) ->
  PosL = lists:map(fun(L) ->   ty_list:transform(L, Ops) end, Pos),
  NegL = lists:map(fun(L) -> N(ty_list:transform(L, Ops)) end, Neg),
  I(PosL ++ NegL).

