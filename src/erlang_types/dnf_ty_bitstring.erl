-module(dnf_ty_bitstring).

-define(ATOM, ty_bitstring).
-define(LEAF, ty_bool).

-include("dnf/bdd.hrl").

-spec is_empty_line({[T], [T], ?LEAF:type()}, S) -> {boolean(), S} when S :: is_empty_cache(), T :: ?ATOM:type().
is_empty_line(Line, ST) ->
  dnf_ty_tuple:is_empty_line(Line, ST).

-spec normalize_line({[T], [T], ?LEAF:type()}, monomorphic_variables(), S) -> {set_of_constraint_sets(), S} when S :: normalize_cache(), T :: ?ATOM:type().
normalize_line(Line, Fixed, ST) ->
  dnf_ty_tuple:normalize_line(Line, Fixed, ST).

-spec all_variables_line([T], [T], ?LEAF:type(), all_variables_cache()) -> sets:set(variable()) when T :: ?ATOM:type().
all_variables_line(P, N, Leaf, Cache) ->
  dnf_ty_tuple:all_variables_line(P, N, Leaf, Cache).
