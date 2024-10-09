-module(dnf_ty_list).

-define(ELEMENT, ty_list).
-define(TERMINAL, bdd_bool).
-define(F(Z), fun() -> Z end).

-export([apply_to_node/3]).
-export([is_empty/1, normalize/5, substitute/4]).
-export([list/1, all_variables/1, transform/2]).

-include("bdd_node.hrl").

list(TyList) -> node(TyList).

% partially generic
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

% module specific implementations
is_empty_coclause(Pos, Neg, T) ->
  case bdd_bool:empty() of
    T -> true;
    _ ->
      Big = ty_list:big_intersect(Pos),
      S1 = ty_list:pi1(Big),
      S2 = ty_list:pi2(Big),
      ty_rec:is_empty(S1) orelse
        ty_rec:is_empty(S2) orelse
        phi(S1, S2, Neg)
  end.

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
  dnf(TyList, {
    fun(Pos, Neg, DnfTyList) ->
      normalize_coclause(Pos, Neg, DnfTyList, Fixed, M)
                                 end,
    fun constraint_set:meet/2
  });
normalize(DnfTyList, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:list(dnf_var_ty_list:list(DnfTyList)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:list(dnf_var_ty_list:var(Var)) end, M).


normalize_coclause([], [], T, _Fixed, _M) ->
  case bdd_bool:empty() of T -> [[]]; _ -> [] end;
normalize_coclause(Pos, Neg, T, Fixed, M) ->
  case bdd_bool:empty() of
    T -> [[]];
    _ ->
      Big = ty_list:big_intersect(Pos),
      S1 = ty_list:pi1(Big),
      S2 = ty_list:pi2(Big),
      phi_norm(S1, S2, Neg, Fixed, M)
  end.

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

apply_to_node(Node, Map, Memo) ->
  substitute(Node, Map, Memo, fun(N, S, M) -> ty_list:substitute(N, S, M) end).
