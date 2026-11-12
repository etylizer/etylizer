-module(subtype_bitstring_tests).
-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

bitstring_test() ->
  true = is_equiv(tbitstring(), tbitstring()).

bitstring_neg_test() ->
  false = is_subtype(tbitstring(), n(tbitstring())).

% <<_:32>> is a nonempty byte-aligned binary
fixed_32_subtype_binary_test() ->
  true = is_subtype(tbitstring_m_n(32, 0), tbinary()).

bitstring_minus_binary_nonempty_test() ->
  false = is_subtype(i(tbitstring(), n(tbinary())), tnone()).

binary_minus_nonempty_binary_is_empty_test() ->
  true = is_equiv(i(tbinary(), n(tnonempty_binary())), tempty_bitstring()).

malformed_cell_is_empty_test() ->
  true = is_subtype({bitstring_cons, tatom(), tany()}, tnone()),
  true = is_subtype({bitstring_cons, tint(0, 1), tatom()}, tnone()).

any_cell_is_nonempty_bitstring_test() ->
  true = is_equiv({bitstring_cons, tany(), tany()}, tnonempty_bitstring()).
