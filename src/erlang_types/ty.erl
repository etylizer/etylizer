-module(ty).

-compile([export_all, nowarn_export_all]).

compare(A, B) -> ty_node:compare(A, B).

any() ->
  ty_node:any().

empty() ->
  ty_node:empty().

