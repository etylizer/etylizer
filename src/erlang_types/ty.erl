-module(ty).

-compile([export_all, nowarn_export_all]).

-export_type([type/0]).

-opaque type() :: ty_node:type().

compare(A, B) -> ty_node:compare(A, B).

any() ->
  ty_node:any().

empty() ->
  ty_node:empty().

all_variables(Ty) ->
  ty_node:all_variables(Ty, #{}).

% subtyping
is_equivalent(T1, T2) ->
  ty_node:leq(T1, T2) andalso ty_node:leq(T2, T1).

% tallying
normalize(Ty, MonomorphicVariables) ->
  ty_node:normalize(Ty, MonomorphicVariables).

substitute(T, Map) ->
  ty_node:substitute(T, Map).

% operators
difference(Ty1, Ty2) -> ty_node:intersect(Ty1, ty_node:negate(Ty2)).
union(Ty1, Ty2) -> ty_node:union(Ty1, Ty2).
intersect(Ty1, Ty2) -> ty_node:intersect(Ty1, Ty2).

% constructors for various levels
atom() ->
  ty_node:make(dnf_ty_variable:atom(dnf_ty_atom:any())).

variable(TyVariable) ->
  ty_node:make(dnf_ty_variable:singleton(TyVariable)).
