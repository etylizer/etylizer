-module(dnf_var_ty_map).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_map).

-export([is_empty_corec/2, normalize_corec/3, substitute/4]).
-export([var/1, map/1, all_variables/2, transform/2, apply_to_node/3]).

% implementations provided by bdd_var.hrl
-include("bdd_var.hrl").

map(Map) -> terminal(Map).
var(Var) -> node(Var).

is_empty_corec(TyBDD, M) -> dnf(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T,M) end, fun is_empty_union/2}).
is_empty_coclause_corec(_Pos, _Neg, T, M) -> dnf_ty_map:is_empty_corec(T, M).

normalize_corec(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTyMap) -> dnf_ty_map:normalize_corec(DnfTyMap, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% substitution delegates to dnf_ty_map substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_map:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_map:substitute(N, Subst, M) end).