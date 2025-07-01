-module(ty).

-compile([export_all, nowarn_export_all]).

-export_type([type/0]).

-opaque type() :: ty_node:type().
-type monomorphic_variables() :: etally:monomorphic_variables().
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type variable() :: ty_variable:type().

-spec compare(T, T) -> eq | lt | gt when T :: type().
compare(A, B) -> ty_node:compare(A, B).

-spec any() -> type().
any() -> ty_node:any().

-spec empty() -> type().
empty() -> ty_node:empty().

-spec all_variables(type()) -> sets:set(variable()).
all_variables(Ty) ->
  ty_node:all_variables(Ty, #{}).

% subtyping
-spec is_equivalent(T, T) -> boolean() when T :: type().
is_equivalent(T1, T2) ->
  ty_node:leq(T1, T2) andalso ty_node:leq(T2, T1).

% tallying
-spec normalize(type(), monomorphic_variables()) -> set_of_constraint_sets().
normalize(Ty, MonomorphicVariables) ->
  ty_node:normalize(Ty, MonomorphicVariables).

-spec substitute(type(), #{variable() => type()}) -> type().
substitute(T, Map) ->
  ty_node:substitute(T, Map).

% operators
-spec difference(T, T) -> T when T :: type().
difference(Ty1, Ty2) -> ty_node:intersect(Ty1, ty_node:negate(Ty2)).

-spec union(T, T) -> T when T :: type().
union(Ty1, Ty2) -> ty_node:union(Ty1, Ty2).

-spec intersect(T, T) -> T when T :: type().
intersect(Ty1, Ty2) -> ty_node:intersect(Ty1, Ty2).

% constructors for various levels
-spec atom() -> type().
atom() ->
  ty_node:make(dnf_ty_variable:atom(dnf_ty_atom:any())).

-spec variable(variable()) -> type().
variable(TyVariable) ->
  ty_node:make(dnf_ty_variable:singleton(TyVariable)).
