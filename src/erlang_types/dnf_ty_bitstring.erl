-module(dnf_ty_bitstring).

-define(ATOM, ty_bitstring).
-define(LEAF, ty_bool).

-include("dnf/bdd.hrl").

-spec is_empty_line({[T], [T], ?LEAF:type()}, S) -> {boolean(), S} when S :: is_empty_cache(), T :: ?ATOM:type().
is_empty_line({Pos, Neg, T}, ST) -> dnf_ty_tuple:is_empty_line({[ty_bitstring:well_formed() | Pos], Neg, T}, ST).

-spec normalize_line({[T], [T], ?LEAF:type()}, monomorphic_variables(), S) -> {set_of_constraint_sets(), S} when S :: normalize_cache(), T :: ?ATOM:type().
normalize_line({Pos, Neg, T}, Fixed, ST) ->
  dnf_ty_tuple:normalize_line({[ty_bitstring:well_formed() | Pos], Neg, T}, Fixed, ST).
