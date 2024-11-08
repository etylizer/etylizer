-module(dnf_ty_list).

-define(ELEMENT, ty_list).
-define(TERMINAL, bdd_bool).
-define(F(Z), fun() -> Z end).

-export([apply_to_node/3]).
-export([is_empty_corec/2, normalize_corec/5, substitute/4]).
-export([list/1, all_variables/2, transform/2]).

-include("bdd_node.hrl").

list(TyList) -> node(TyList).

% partially generic
is_empty_corec(TyBDD, M) -> dnf(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2}).

% module specific implementations
is_empty_coclause_corec(Pos, Neg, T, M) ->
  case bdd_bool:empty() of
    T -> true;
    _ ->
      Big = ty_list:big_intersect(Pos),
      S1 = ty_list:pi1(Big),
      S2 = ty_list:pi2(Big),
      ty_rec:is_empty_corec(S1, M) orelse
        ty_rec:is_empty_corec(S2, M) orelse
        phi_corec(S1, S2, Neg, M)
  end.

phi_corec(S1, S2, [], M) ->
  ty_rec:is_empty_corec(S1, M)
    orelse
    ty_rec:is_empty_corec(S2, M);
phi_corec(S1, S2, [Ty | N], M) ->
  ty_rec:is_empty_corec(S1, M)
    orelse ty_rec:is_empty_corec(S2, M)
    orelse (
      begin
        T1 = ty_list:pi1(Ty),
        T2 = ty_list:pi2(Ty),
        phi_corec(ty_rec:diff(S1, T1), S2, N, M)
          andalso
          phi_corec(S1, ty_rec:diff(S2, T2), N, M)
      end
  ).

normalize_corec(TyList, [], [], Fixed, M) ->
  dnf(TyList, {
    fun(Pos, Neg, DnfTyList) ->
      normalize_coclause_corec(Pos, Neg, DnfTyList, Fixed, M)
                                 end,
    fun constraint_set:meet/2
  });
normalize_corec(DnfTyList, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:list(dnf_var_ty_list:list(DnfTyList)),
  % ntlv rule
  ty_variable:normalize_corec(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:list(dnf_var_ty_list:var(Var)) end, M).


normalize_coclause_corec([], [], T, _Fixed, _M) ->
  case bdd_bool:empty() of T -> [[]]; _ -> [] end;
normalize_coclause_corec(Pos, Neg, T, Fixed, M) ->
  case bdd_bool:empty() of
    T -> [[]];
    _ ->
      Big = ty_list:big_intersect(Pos),
      S1 = ty_list:pi1(Big),
      S2 = ty_list:pi2(Big),
      phi_norm_corec(S1, S2, Neg, Fixed, M)
  end.

phi_norm_corec(S1, S2, [], Fixed, M) ->
  T1 = ?F(ty_rec:normalize_corec(S1, Fixed, M)),
  T2 = ?F(ty_rec:normalize_corec(S2, Fixed, M)),
  constraint_set:join(T1, T2);
phi_norm_corec(S1, S2, [Ty | N], Fixed, M) ->
  T1 = ?F(ty_rec:normalize_corec(S1, Fixed, M)),
  T2 = ?F(ty_rec:normalize_corec(S2, Fixed, M)),

  T3 =
    ?F(begin
      TT1 = ty_list:pi1(Ty),
      TT2 = ty_list:pi2(Ty),
      X1 = ?F(phi_norm_corec(ty_rec:diff(S1, TT1), S2, N, Fixed, M)),
      X2 = ?F(phi_norm_corec(S1, ty_rec:diff(S2, TT2), N, Fixed, M)),
      constraint_set:meet(X1, X2)
    end),

  constraint_set:join(T1, ?F(constraint_set:join(T2, T3))).

apply_to_node(Node, Map, Memo) ->
  error(todo),
  substitute(Node, Map, Memo, fun(N, S, M) -> ty_list:substitute(N, S, M) end).
