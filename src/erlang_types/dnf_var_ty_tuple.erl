-module(dnf_var_ty_tuple).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_tuple).
-define(F(Z), fun() -> Z end).

-export([normalize/4, substitute/4]).
-export([var/1, tuple/1, all_variables/1, mall_variables/1, transform/2, is_empty/1, apply_to_node/3, to_singletons/1]).

% implementations provided by bdd_var.hrl
-include("bdd_var.hrl").

tuple(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_tuple:is_empty(T).

mall_variables({Default, Others}) when is_map(Others) ->
  lists:usort(lists:flatten(
    all_variables(Default) ++
    lists:map(fun({_K,V}) -> all_variables(V) end, maps:to_list(Others))
  ));
mall_variables(Ty) -> all_variables(Ty).

normalize(Size, Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTy) -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
  fun constraint_set:meet/2
}).

normalize_coclause(Size, PVar, NVar, Tuple, Fixed, M) ->
  case dnf_ty_tuple:empty() of
    Tuple -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized(Tuple, Fixed, M) of
        true ->
          % TODO test case
          error({todo, extract_test_case, memoize_tuple}); %[[]];
        miss ->
          % memoize only non-variable component t0
          dnf_ty_tuple:normalize(Size, Tuple, PVar, NVar, Fixed, sets:union(M, sets:from_list([Tuple])))
      end
  end.

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_tuple:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_tuple:substitute(N, Subst, M) end).

to_singletons(TyBDD) -> dnf(TyBDD, {
  fun(_Pos = [], _Neg = [], T) -> dnf_ty_tuple:to_singletons(T); (_, _, _) -> [] end,
  fun(F1, F2) -> F1() ++ F2() end
}).