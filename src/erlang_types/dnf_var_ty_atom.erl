-module(dnf_var_ty_atom).

-define(P, {ty_atom, ty_variable}).

-export([equal/2, compare/2]).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/3, substitute/4]).
-export([ty_var/1, ty_atom/1, all_variables/1]).
-export([transform/2]).

ty_atom(Atom) -> gen_bdd:terminal(?P, Atom).
ty_var(Var) -> gen_bdd:element(?P, Var).

% generic
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).
union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).
is_any(B) -> gen_bdd:is_any(?P, B).
equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).
substitute(MkTy, T, M, _) -> gen_bdd:substitute(?P, MkTy, T, M, sets:new()).
all_variables(TyBDD) -> gen_bdd:all_variables(?P, TyBDD).
transform(Ty, Ops) -> gen_bdd:transform(?P, Ty, Ops).

% partially generic
is_empty(TyBDD) -> gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).

is_empty_coclause(_Pos, _Neg, T) -> ty_atom:is_empty(T).

normalize(Ty, Fixed, M) -> gen_bdd:dnf(?P, Ty, {
  fun(Pos, Neg, Atom) -> ty_atom:normalize(Atom, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

