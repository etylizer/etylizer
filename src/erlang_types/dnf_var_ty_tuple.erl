
-module(dnf_var_ty_tuple).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_product).
-define(F(Z), fun() -> Z end).

-export([normalize/4, substitute/4]).
-export([var/1, tuple/1, all_variables/2, mall_variables/2, transform/2, is_empty/1, apply_to_node/3]).

% implementations provided by bdd_var.hrl
-include("bdd_var.hrl").

tuple(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_product:is_empty(T).

mall_variables({Default, T0, T1, Others}, M) when is_map(Others) ->
  lists:usort(lists:flatten(
    dnf_var_ty_bool:all_variables(T0, M) ++
    dnf_var_ty_ref:all_variables(T1, M) ++
    all_variables(Default, M) ++
    lists:map(fun({_K,V}) -> all_variables(V, M) end, maps:to_list(Others))
  ));
mall_variables(Ty, M) -> all_variables(Ty, M).

normalize(Size, Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTy) -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
  fun constraint_set:meet/2
}).

normalize_coclause(Size, PVar, NVar, Tuple, Fixed, M) ->
  case dnf_ty_product:empty() of
    Tuple -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized({PVar, NVar, Tuple}, Fixed, M) of
        true ->
          [[]];
        miss ->
          dnf_ty_product:normalize(Size, Tuple, PVar, NVar, Fixed, sets:union(M, sets:from_list([{PVar, NVar, Tuple}])))
      end
  end.

% substitution delegates to dnf_ty_product substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_product:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_tuple:substitute(N, Subst, M) end).
