-module(subtype_bitstring_tests).
-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

bitstring_test() ->
  true = is_equiv(tbitstring(), tbitstring()).

bitstring_neg_test() ->
  false = is_subtype(tbitstring(), n(tbitstring())).
