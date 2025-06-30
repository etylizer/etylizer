-module(ty).

-compile([export_all, nowarn_export_all]).

compare(A, B) -> ty_node:compare(A, B).

any() ->
  ty_node:any().

empty() ->
  ty_node:empty().

all_variables(Ty) ->
  ty_node:all_variables(Ty, #{}).

is_equivalent(T1, T2) ->
  ty_node:leq(T1, T2) andalso ty_node:leq(T2, T1).

substitute(T, Map) ->
  ty_node:substitute(T, Map).

% constructors for various levels
atom() ->
  ty_node:make(dnf_ty_variable:atom(dnf_ty_atom:any())).

variable(TyVariable) ->
  ty_node:make(dnf_ty_variable:singleton(TyVariable)).
