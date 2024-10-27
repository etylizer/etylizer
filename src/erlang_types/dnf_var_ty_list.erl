-module(dnf_var_ty_list).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_list).

-export([is_empty_corec/2, normalize/3, substitute/4]).
-export([var/1, list/1, all_variables/2, transform/2, apply_to_node/3]).

-include("bdd_var.hrl").

% fully generic
list(List) -> terminal(List).
var(Var) -> node(Var).

% partially generic
is_empty_coclause_corec(_Pos, _Neg, T, M) -> dnf_ty_list:is_empty_corec(T, M).
is_empty_corec(TyBDD, M) -> dnf(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2}).
normalize(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTyList) -> normalize_coclause(Pos, Neg, DnfTyList, Fixed, M) end,
  fun constraint_set:meet/2
}).

% module specific implementations
normalize_coclause(PVar, NVar, List, Fixed, M) ->
  case dnf_ty_list:empty() of
    List -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized({PVar, NVar, List}, Fixed, M) of
        true ->
          [[]];
        miss ->
          dnf_ty_list:normalize(List, PVar, NVar, Fixed, sets:union(M, sets:from_list([{PVar, NVar, List}])))
      end
  end.



% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_list:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_list:substitute(N, Subst, M) end).
