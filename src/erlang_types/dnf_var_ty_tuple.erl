-module(dnf_var_ty_tuple).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_tuple).
-define(F(Z), fun() -> Z end).

-export([equal_all/2]).

-export([normalize_corec/4, substitute/4]).
-export([var/1, tuple/1, all_variables/2, mall_variables/2, transform/2, is_empty_corec/2, apply_to_node/3]).

% implementations provided by bdd_var.hrl
-include("bdd_var.hrl").

equal_all({DefaultT1, T1}, {DefaultT2, T2}) -> 
  % TODO test case: 
  %      we could filter here equivalent representations with left-over
  %      empty and any tuples, e.q. {0, #{1 => Empty}} =:= {0, #{}}
  dnf_var_ty_tuple:equal(DefaultT1, DefaultT2) andalso maps:size(T1) =:= maps:size(T2) andalso
  % minor improvement: don't iterate over all sizes after false is encountered
  maps:map(fun(Size, T, Res) -> Res andalso dnf_var_ty_tuple:equal(T, maps:get(Size, T2)) end, true, T1).

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

normalize_corec(Size, Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTy) -> dnf_ty_tuple:normalize_corec(Size, DnfTy, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_tuple:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_tuple:substitute(N, Subst, M) end).