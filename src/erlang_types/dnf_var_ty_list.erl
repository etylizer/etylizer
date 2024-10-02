-module(dnf_var_ty_list).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_list).

-export([is_empty/1,normalize/3, substitute/4]).
-export([var/1, list/1, all_variables/1, transform/2, apply_to_node/3]).

-include("bdd_var.hrl").

% fully generic
list(List) -> terminal(List).
var(Var) -> node(Var).

% partially generic
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_list:is_empty(T).
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
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
          % TODO test case
          error({todo, extract_test_case, memoize_function}); %[[]];
        miss ->
          dnf_ty_list:normalize(List, PVar, NVar, Fixed, sets:union(M, sets:from_list([{PVar, NVar, List}])))
      end
  end.



% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_list:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_list:substitute(N, Subst, M) end).
