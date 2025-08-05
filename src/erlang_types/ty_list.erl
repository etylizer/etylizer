-module(ty_list).

-export([
  equal/2,
  compare/2,
  unparse/2,
  list/1
]).

-export_type([type/0]).

-type type() :: ty_tuple:type().
-type ast_ty() :: ast:ty().

-spec list([ty_node:type()]) -> type().
list(Refs) -> ty_tuple:tuple(Refs).

-spec compare(type(), type()) -> eq | lt | gt.
compare(A, B) -> ty_tuple:compare(A, B).

-spec equal(type(), type()) -> boolean().
equal(P1, P2) -> ty_tuple:equal(P1, P2).

-spec unparse(type(), T) -> {ast_ty(), T}.
unparse({ty_tuple, 2, [List, Termination]}, ST0) ->
  {L1, ST1} = ty_node:unparse(List, ST0),
  {L2, ST2} = ty_node:unparse(Termination, ST1),
  {{improper_list, L1, L2}, ST2}.

