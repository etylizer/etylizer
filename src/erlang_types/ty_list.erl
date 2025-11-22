-module(ty_list).

-export([
  equal/2,
  compare/2,
  unparse/2,
  list/1
]).

-export_type([type/0]).

% invariants
-etylizer({disable_exhaustiveness_toplevel, [unparse/2]}).

-include("erlang_types.hrl").
-include("etylizer.hrl").


% we can't make it more precise
% because Erlang does not support list types with a fixed amount of elements
-type type() :: ty_tuple:type().

-spec list([ty_node:type()]) -> type().
list(Refs) -> 
    ?assert_pattern(2, length(Refs)),
    ty_tuple:tuple(Refs).

-spec compare(type(), type()) -> eq | lt | gt.
compare(A, B) -> ty_tuple:compare(A, B).

-spec equal(type(), type()) -> boolean().
equal(P1, P2) -> ty_tuple:equal(P1, P2).

-spec unparse(type(), T) -> {ast_ty(), T} when T :: unparse_cache().
unparse({ty_tuple, 2, [List, Termination]}, ST0) ->
  {L1, ST1} = ty_node:unparse(List, ST0),
  {L2, ST2} = ty_node:unparse(Termination, ST1),
  {{cons, L1, L2}, ST2}.

