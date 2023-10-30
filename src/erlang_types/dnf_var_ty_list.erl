-module(dnf_var_ty_list).

-define(P, {dnf_ty_list, ty_variable}).

-export([equal/2, compare/2]).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/3, substitute/4]).
-export([var/1, list/1, all_variables/1, has_ref/2, transform/2, get_dnf/1]).

% fully generic
list(List) -> gen_bdd:terminal(?P, List).
var(Var) -> gen_bdd:element(?P, Var).
has_ref(Ty, Ref) -> gen_bdd:has_ref(?P, Ty, Ref).
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
all_variables(TyBDD) -> gen_bdd:all_variables(?P, TyBDD).
transform(Ty, Ops) -> gen_bdd:transform(?P, Ty, Ops).
get_dnf(Bdd) -> gen_bdd:get_dnf(?P, Bdd).

% partially generic
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_list:is_empty(T).
is_empty(TyBDD) -> gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).
normalize(Ty, Fixed, M) -> gen_bdd:dnf(?P, Ty, {
  fun(Pos, Neg, DnfTyList) -> normalize_coclause(Pos, Neg, DnfTyList, Fixed, M) end,
  fun constraint_set:meet/2
}).

% module specific implementations
normalize_coclause(PVar, NVar, List, Fixed, M) ->
  case dnf_ty_list:empty() of
    List -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized(List, Fixed, M) of
        true ->
          % TODO test case
          error({todo, extract_test_case, memoize_function}); %[[]];
        miss ->
          % memoize only non-variable component t0
          dnf_ty_list:normalize(List, PVar, NVar, Fixed, sets:union(M, sets:from_list([List])))
      end
  end.
