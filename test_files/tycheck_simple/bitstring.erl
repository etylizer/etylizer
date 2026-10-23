-module(bitstring).

-compile([export_all, nowarn_export_all]).

% === empty bitstrings

-spec b1() -> <<_:0, _:_*0>>.
b1() -> <<>>.

-spec b1_alias1() -> <<>>.
b1_alias1() -> <<>>.

-spec b1_alias2() -> <<_:_*0>>.
b1_alias2() -> <<>>.

-spec b1_alias3() -> <<_:0>>.
b1_alias3() -> <<>>.

-spec b1_alias4() -> binary().
b1_alias4() ->
  <<>>.

% constant type operator evaluations
-spec b1_constant1() -> <<_:0, _:_*(0+0)>>.
b1_constant1() -> <<>>.

-spec b1_constant2() -> <<_:0, _:_*((-1)+1)>>.
b1_constant2() -> <<>>.

-spec b1_constant3() -> <<_:0, _:_*(0*10)>>.
b1_constant3() -> <<>>.

-spec b1_fail() -> <<>>.
b1_fail() -> ok.

-spec b2_fail(<<>> | integer()) -> ok.
b2_fail(X) when is_integer(X) -> ok.

-spec b3() -> binary().
b3() ->
    X = 3,
    <<A:X/binary, B/binary>> = <<"abcde">>,
    case is_binary(A) of
      true -> ok;
      false -> ok
    end,
    B.

-spec b4_fail() -> binary().
b4_fail() ->
    X = not_int,
    <<_:X/binary, B/binary>> = <<"abcde">>,
    B.

-spec b5() -> bitstring().
b5() ->
  <<"abc">> = <<(<<"abc">>)/bitstring>>,
  <<"abc">> = <<(<<"abc">>)/binary-unit:1>>,
  <<"abc">> = <<(<<"abc">>)/binary>>,
  <<1:1>> = <<(<<1:1>>)/bitstring>>,
  <<1:1>> = <<(<<1:1>>)/binary-unit:1>>,
  <<_/binary-unit:16>> = <<"">>,
  <<_/binary-unit:16>> = <<"ab">>,
  <<_/binary-unit:16>> = <<"abcd">>,
  <<"ab">> = <<(<<"abc">>):2/binary>>,
  <<>>.


% ============================================================
% === Construction
% ============================================================

% Construct a bitstring (3 bits, not byte-aligned)
-spec bin_construct_int_06(integer()) -> bitstring().
bin_construct_int_06(X) -> <<X:3>>.

% Construct with variable size
-spec bin_construct_int_09(integer(), integer()) -> bitstring().
bin_construct_int_09(X, Size) -> <<X:Size>>.

% Concatenate two binaries
-spec bin_construct_bin_01(binary(), binary()) -> binary().
bin_construct_bin_01(A, B) -> <<A/binary, B/binary>>.

% Unit-based construction: result is multiple of 6 bits
-spec bin_construct_unit_01(integer(), integer()) -> <<_:_*6>>.
bin_construct_unit_01(A, B) ->
    <<0:A/integer-unit:36, 1:B/integer-unit:30>>.

% 32-bit binary from four bytes
-spec bin_precise_01() -> <<_:32>>.
bin_precise_01() -> <<1, 2, 3, 4>>.

-spec bin_exp_01(binary()) -> nonempty_binary().
bin_exp_01(Buf) -> <<Buf/binary, $">>.

-spec bin_exp_02_fail(<<_:16>>) -> <<_:32>>.
bin_exp_02_fail(B) -> <<1, B/binary>>.

-spec bin_exp_08(binary(), integer()) -> bitstring().
bin_exp_08(A, N) -> <<A:N/binary, 1:3>>.

-spec bin_exp_08_fail(binary(), integer()) -> binary().
bin_exp_08_fail(A, N) -> <<A:N/binary, 1:3>>.

% Atom where integer expected in construction
-spec bin_type_error_05_fail(atom()) -> binary().
bin_type_error_05_fail(X) -> <<X>>.

% bitstring() is no subtype of binary()
-spec bin_subtype_01_fail() -> binary().
bin_subtype_01_fail() -> <<1:1>>.

% With a size, a binary segment takes the first Size bytes of any bitstring
-spec bin_construct_bin_02(bitstring()) -> <<_:8>>.
bin_construct_bin_02(B) -> <<B:1/binary>>.

% Without a size, the value is a whole number of units
-spec bin_type_error_06_fail(<<_:8>>) -> <<_:_*16>>.
bin_type_error_06_fail(B) -> <<B/binary-unit:16>>.

% A string is a sequence of integer segments, no binary
-spec bin_type_error_07_fail() -> binary().
bin_type_error_07_fail() -> <<"abc"/binary>>.

-spec bin_construct_string_01() -> <<_:48>>.
bin_construct_string_01() -> <<"abc":16>>.
