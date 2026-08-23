-module(subtype_bitstring_tests).
-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

% === Reflexivity ===

bitstring_refl_test() ->
  true = is_equiv(tbitstring(), tbitstring()).

binary_refl_test() ->
  true = is_equiv(tbinary(), tbinary()).

nonempty_binary_refl_test() ->
  true = is_equiv(tnonempty_binary(), tnonempty_binary()).

nonempty_bitstring_refl_test() ->
  true = is_equiv(tnonempty_bitstring(), tnonempty_bitstring()).

empty_bitstring_refl_test() ->
  true = is_equiv(tempty_bitstring(), tempty_bitstring()).

% === Negation ===

bitstring_neg_test() ->
  false = is_subtype(tbitstring(), n(tbitstring())).

binary_neg_test() ->
  false = is_subtype(tbinary(), n(tbinary())).

% === binary() <= bitstring() ===

binary_subtype_bitstring_test() ->
  true = is_subtype(tbinary(), tbitstring()).

bitstring_not_subtype_binary_test() ->
  false = is_subtype(tbitstring(), tbinary()).

% === nonempty_binary() <= binary() ===

nonempty_binary_subtype_binary_test() ->
  true = is_subtype(tnonempty_binary(), tbinary()).

binary_not_subtype_nonempty_binary_test() ->
  false = is_subtype(tbinary(), tnonempty_binary()).

% === nonempty_binary() <= bitstring() ===

nonempty_binary_subtype_bitstring_test() ->
  true = is_subtype(tnonempty_binary(), tbitstring()).

% === nonempty_bitstring() <= bitstring() ===

nonempty_bitstring_subtype_bitstring_test() ->
  true = is_subtype(tnonempty_bitstring(), tbitstring()).

bitstring_not_subtype_nonempty_bitstring_test() ->
  false = is_subtype(tbitstring(), tnonempty_bitstring()).

% === nonempty_binary() <= nonempty_bitstring() ===

nonempty_binary_subtype_nonempty_bitstring_test() ->
  true = is_subtype(tnonempty_binary(), tnonempty_bitstring()).

nonempty_bitstring_not_subtype_nonempty_binary_test() ->
  false = is_subtype(tnonempty_bitstring(), tnonempty_binary()).

% === nonempty_bitstring() is NOT a subtype of binary() ===
% (non-byte-aligned bitstrings exist in nonempty_bitstring but not in binary)

nonempty_bitstring_not_subtype_binary_test() ->
  false = is_subtype(tnonempty_bitstring(), tbinary()).

% === empty bitstring (<<>>) ===

empty_subtype_binary_test() ->
  true = is_subtype(tempty_bitstring(), tbinary()).

empty_subtype_bitstring_test() ->
  true = is_subtype(tempty_bitstring(), tbitstring()).

empty_not_subtype_nonempty_binary_test() ->
  false = is_subtype(tempty_bitstring(), tnonempty_binary()).

empty_not_subtype_nonempty_bitstring_test() ->
  false = is_subtype(tempty_bitstring(), tnonempty_bitstring()).

% === Fixed-size bitstrings via {bitstring, M, N} ===

% <<_:32>> is a nonempty byte-aligned binary
fixed_32_subtype_binary_test() ->
  true = is_subtype(tbitstring_m_n(32, 0), tbinary()).

fixed_32_subtype_bitstring_test() ->
  true = is_subtype(tbitstring_m_n(32, 0), tbitstring()).

fixed_32_subtype_nonempty_binary_test() ->
  true = is_subtype(tbitstring_m_n(32, 0), tnonempty_binary()).

fixed_32_subtype_nonempty_bitstring_test() ->
  true = is_subtype(tbitstring_m_n(32, 0), tnonempty_bitstring()).

% <<_:5>> is a non-byte-aligned bitstring
fixed_5_subtype_bitstring_test() ->
  true = is_subtype(tbitstring_m_n(5, 0), tbitstring()).

fixed_5_not_subtype_binary_test() ->
  false = is_subtype(tbitstring_m_n(5, 0), tbinary()).

fixed_5_subtype_nonempty_bitstring_test() ->
  true = is_subtype(tbitstring_m_n(5, 0), tnonempty_bitstring()).

fixed_5_not_subtype_nonempty_binary_test() ->
  false = is_subtype(tbitstring_m_n(5, 0), tnonempty_binary()).

% === Unit-based types ===

% <<_:_*16>> has sizes {0, 16, 32, ...} - all multiples of 8 -> subset of binary
unit_16_subtype_binary_test() ->
  true = is_subtype(tbitstring_m_n(0, 16), tbinary()).

% <<_:_*3>> has sizes {0, 3, 6, 9, 12, ...} - includes non-multiples of 8
unit_3_not_subtype_binary_test() ->
  false = is_subtype(tbitstring_m_n(0, 3), tbinary()).

unit_3_subtype_bitstring_test() ->
  true = is_subtype(tbitstring_m_n(0, 3), tbitstring()).

% === Equivalences ===

% binary() == <<_:_*8>>
binary_equiv_unit8_test() ->
  true = is_equiv(tbinary(), tbitstring_m_n(0, 8)).

% bitstring() == <<_:_*1>>
bitstring_equiv_unit1_test() ->
  true = is_equiv(tbitstring(), tbitstring_m_n(0, 1)).

% nonempty_binary() == <<_:8, _:_*8>>
nonempty_binary_equiv_test() ->
  true = is_equiv(tnonempty_binary(), tbitstring_m_n(8, 8)).

% nonempty_bitstring() == <<_:1, _:_*1>>
nonempty_bitstring_equiv_test() ->
  true = is_equiv(tnonempty_bitstring(), tbitstring_m_n(1, 1)).

% <<>> == <<_:0, _:_*0>>
empty_equiv_test() ->
  true = is_equiv(tempty_bitstring(), tbitstring_m_n(0, 0)).

% === Union/Intersection relationships ===

% binary() | nonempty_bitstring() = bitstring()
union_binary_nonempty_bitstring_is_bitstring_test() ->
  true = is_equiv(u(tbinary(), tnonempty_bitstring()), tbitstring()).

% binary() & nonempty_bitstring() = nonempty_binary()
intersect_binary_nonempty_bitstring_is_nonempty_binary_test() ->
  true = is_equiv(i(tbinary(), tnonempty_bitstring()), tnonempty_binary()).

% empty_bitstring() | nonempty_binary() = binary()
union_empty_nonempty_binary_is_binary_test() ->
  true = is_equiv(u(tempty_bitstring(), tnonempty_binary()), tbinary()).

% empty_bitstring() | nonempty_bitstring() = bitstring()
union_empty_nonempty_bitstring_is_bitstring_test() ->
  true = is_equiv(u(tempty_bitstring(), tnonempty_bitstring()), tbitstring()).

% === Cross-type: bitstrings are disjoint from other types ===

bitstring_disjoint_integer_test() ->
  false = is_subtype(tbitstring(), tint()).

integer_disjoint_bitstring_test() ->
  false = is_subtype(tint(), tbitstring()).

binary_disjoint_atom_test() ->
  false = is_subtype(tbinary(), tatom()).

bitstring_disjoint_float_test() ->
  false = is_subtype(tbitstring(), tfloat()).

% === Top/bottom relationships ===

none_subtype_bitstring_test() ->
  true = is_subtype(tnone(), tbitstring()).

none_subtype_binary_test() ->
  true = is_subtype(tnone(), tbinary()).

bitstring_subtype_any_test() ->
  true = is_subtype(tbitstring(), tany()).

binary_subtype_any_test() ->
  true = is_subtype(tbinary(), tany()).

% === Negation with specific types ===

% bitstring() & ~binary() is non-empty (the non-byte-aligned part)
bitstring_minus_binary_nonempty_test() ->
  false = is_subtype(i(tbitstring(), n(tbinary())), tnone()).

% binary() & ~nonempty_binary() = empty_bitstring()
binary_minus_nonempty_binary_is_empty_test() ->
  true = is_equiv(i(tbinary(), n(tnonempty_binary())), tempty_bitstring()).

% bitstring() & ~nonempty_bitstring() = empty_bitstring()
bitstring_minus_nonempty_bitstring_is_empty_test() ->
  true = is_equiv(i(tbitstring(), n(tnonempty_bitstring())), tempty_bitstring()).
