-module(dnf_var_ty_tuple).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_tuple).
-define(F(Z), fun() -> Z end).

-export([normalize/4, substitute/4]).
-export([var/1, tuple/1, all_variables/2, mall_variables/2, transform/2, is_empty_corec/2, apply_to_node/3, to_singletons/1]).

% implementations provided by bdd_var.hrl
-include("bdd_var.hrl").

tuple(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

is_empty_corec(TyBDD, M) -> dnf(TyBDD, {fun(P, N, T)  -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2}).
is_empty_coclause_corec(_Pos, _Neg, T, M) -> dnf_ty_tuple:is_empty_corec(T, M).

mall_variables({Default, Others}, M) when is_map(Others) ->
  lists:usort(lists:flatten(
    all_variables(Default, M) ++
    lists:map(fun({_K,V}) -> all_variables(V, M) end, maps:to_list(Others))
  ));
mall_variables(Ty, M) -> all_variables(Ty, M).

normalize(Size, Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTy) -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
  fun constraint_set:meet/2
}).

normalize_coclause(Size, PVar, NVar, Tuple, Fixed, M) ->
  case dnf_ty_tuple:empty() of
    Tuple -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized({PVar, NVar, Tuple}, Fixed, M) of
        true ->
          [[]];
        miss ->
          dnf_ty_tuple:normalize(Size, Tuple, PVar, NVar, Fixed, sets:union(M, sets:from_list([{PVar, NVar, Tuple}])))
      end
  end.

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_tuple:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_tuple:substitute(N, Subst, M) end).

to_singletons(TyBDD) -> dnf(TyBDD, {
  fun(_Pos = [], _Neg = [], T) -> dnf_ty_tuple:to_singletons(T); (_, _, _) -> [] end,
  fun(F1, F2) -> F1() ++ F2() end
}).