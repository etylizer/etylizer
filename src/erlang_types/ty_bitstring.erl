-module(ty_bitstring).

-export([
  equal/2,
  compare/2,
  unparse/2,
  bitstring_cons/1
]).

-export_type([type/0]).

-include("erlang_types.hrl").
-include("etylizer.hrl").

% A bitstring cons cell: {SegmentHeadType, RestBitstringType}
% Encoded as a 2-tuple, analogous to how ty_list encodes cons cells.
-type type() :: ty_tuple:type().

-spec bitstring_cons([ty_node:type()]) -> type().
bitstring_cons(Refs) ->
    ?assert_pattern(2, length(Refs)),
    ty_tuple:tuple(Refs).

-spec compare(type(), type()) -> eq | lt | gt.
compare(A, B) -> ty_tuple:compare(A, B).

-spec equal(type(), type()) -> boolean().
equal(P1, P2) -> ty_tuple:equal(P1, P2).

-spec unparse(type(), T) -> {ast_ty(), T} when T :: unparse_cache().
unparse({ty_tuple, 2, [Head, Tail]}, ST0) ->
  {H, ST1} = ty_node:unparse(Head, ST0),
  {T, ST2} = ty_node:unparse(Tail, ST1),
  {{bitstring_cons, H, T}, ST2}.
