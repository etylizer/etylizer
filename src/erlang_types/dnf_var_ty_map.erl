-module(dnf_var_ty_map).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_map).

-export([is_empty_corec/2,normalize/3, substitute/4]).
-export([var/1, map/1, all_variables/2, transform/2, apply_to_node/3]).

% implementations provided by bdd_var.hrl
-include("bdd_var.hrl").

map(Map) -> terminal(Map).
var(Var) -> node(Var).

is_empty_corec(TyBDD, M) -> dnf(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T,M) end, fun is_empty_union/2}).
is_empty_coclause_corec(_Pos, _Neg, T, M) -> dnf_ty_map:is_empty_corec(T, M).

normalize(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTyMap) -> normalize_coclause(Pos, Neg, DnfTyMap, Fixed, M) end,
  fun constraint_set:meet/2
}).

normalize_coclause(PVar, NVar, Map, Fixed, M) ->
  case dnf_ty_map:empty() of
    Map -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized({PVar, NVar, Map}, Fixed, M) of
        true ->
          [[]];
        miss ->
          dnf_ty_map:normalize(Map, PVar, NVar, Fixed, sets:union(M, sets:from_list([{PVar, NVar, Map}])))
      end
  end.


% substitution delegates to dnf_ty_map substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_map:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_map:substitute(N, Subst, M) end).