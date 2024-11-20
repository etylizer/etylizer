-module(dnf_var_ty_function).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_function).
-define(F(Z), fun() -> Z end).


-export([is_empty_corec/2]).
-export([normalize_corec/4, substitute/4]).
-export([var/1, function/1, all_variables/2, transform/2]).

-include("bdd_var.hrl").

function(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

is_empty_corec(TyBDD, M) -> dnf(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2}).
is_empty_coclause_corec(_Pos, _Neg, T, M) -> dnf_ty_function:is_empty_corec(T, M).

normalize_corec(Size, Ty, Fixed, M) -> dnf(Ty, {
  fun(PVar, NVar, DnfTy) -> dnf_ty_function:normalize_corec(Size, DnfTy, PVar, NVar, Fixed, M) end,
  fun constraint_set:meet/2
}).

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_function:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_function:substitute(N, Subst, M) end).
