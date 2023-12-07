-module(dnf_var_ty_function).

-define(P, {dnf_ty_function, ty_variable}).
-define(F(Z), fun() -> Z end).


-export([equal/2, compare/2, is_empty/1]).

%%
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_any/1, normalize/4, substitute/4]).

-export([var/1, function/1, all_variables/1, has_ref/2, transform/2, get_dnf/1]).

function(Tuple) -> gen_bdd:terminal(?P, Tuple).
var(Var) -> gen_bdd:element(?P, Var).
transform(Ty, Ops) -> gen_bdd:transform(?P, Ty, Ops).
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).
union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).
is_any(B) -> gen_bdd:is_any(?P, B).
equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).
substitute(MkTy, T, M, Memo) -> gen_bdd:substitute(?P, MkTy, T, M, Memo).
has_ref(Ty, Ref) -> gen_bdd:has_ref(?P, Ty, Ref).
get_dnf(Bdd) -> gen_bdd:get_dnf(?P, Bdd).

all_variables({Default, Others}) when is_map(Others) ->
  lists:usort(lists:flatten(
    gen_bdd:all_variables(?P, Default) ++
    lists:map(fun({_K,V}) -> gen_bdd:all_variables(?P, V) end, maps:to_list(Others))
  ));
all_variables(Ty) -> gen_bdd:all_variables(?P, Ty).

is_empty(TyBDD) -> gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_function:is_empty(T).

normalize(Size, Ty, Fixed, M) -> gen_bdd:dnf(?P, Ty, {
  fun(Pos, Neg, DnfTy) -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
  fun constraint_set:meet/2
}).

normalize_coclause(Size, PVar, NVar, Function, Fixed, M) ->
  case dnf_ty_function:empty() of
    Function -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized(Function, Fixed, M) of
        true ->
          % TODO test case
          error({todo, extract_test_case, memoize_function}); %[[]];
        miss ->
          % memoize only non-variable component t0
          dnf_ty_function:normalize(Size, Function, PVar, NVar, Fixed, sets:union(M, sets:from_list([Function])))
      end
  end.
