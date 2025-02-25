-module(dnf_var_ty_predef).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_predef).

-export([apply_to_node/3]).
-export([is_empty/1, normalize_corec/3, substitute/4]).
-export([var/1, predef/1]).

-include("dnf/bdd_var.hrl").

% generic
predef(Predef) -> terminal(Predef).
var(Var) -> node(Var).

% partially generic
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_predef:is_empty(T).

normalize_corec(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, Atom) -> dnf_ty_predef:normalize_corec(Atom, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% not recursive, no op substitution
apply_to_node(Node, _StdMap, _Memo) ->
  Node.
