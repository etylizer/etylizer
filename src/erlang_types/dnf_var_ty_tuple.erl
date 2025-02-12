-module(dnf_var_ty_tuple).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_tuple).
-define(F(Z), fun() -> Z end).

-export([normalize_corec/4, substitute/4]).
-export([var/1, tuple/1, is_empty_corec/2, apply_to_node/3]).

% implementations provided by bdd_var.hrl
-include("dnf/bdd_var.hrl").

tuple(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

is_empty_corec(TyBDD, M) -> dnf(TyBDD, {fun(P, N, T)  -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2}).
is_empty_coclause_corec(_Pos, _Neg, T, M) -> dnf_ty_tuple:is_empty_corec(T, M).

normalize_corec(Size, Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTy) -> dnf_ty_tuple:normalize_corec(Size, DnfTy, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_tuple:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_tuple:substitute(N, Subst, M) end).