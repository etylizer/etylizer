-module(dnf_var_ty_map).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_map).

-export([is_empty/1,normalize/3, substitute/4]).
-export([var/1, map/1, all_variables/1, transform/2, apply_to_node/3]).

% implementations provided by bdd_var.hrl
-include("bdd_var.hrl").

map(Map) -> terminal(Map).
var(Var) -> node(Var).

is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_map:is_empty(T).

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
          error({todo, extract_test_case, memoize_function}); %[[]];
        miss ->
          dnf_ty_map:normalize(Map, PVar, NVar, Fixed, sets:union(M, sets:from_list([{PVar, NVar, Map}])))
      end
  end.


% substitution delegates to dnf_ty_map substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_map:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_map:substitute(N, Subst, M) end).