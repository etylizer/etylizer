-module(bitstring).

-compile([export_all, nowarn_export_all]).

-include("etylizer.hrl").

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

-spec b1_fail() -> <<>>.
b1_fail() -> ok.

-spec b2_fail(<<>> | integer()) -> ok.
b2_fail(X) when is_integer(X) -> ok.

% a size known at run time only: the match is not proven
-spec b3_fail() -> binary().
b3_fail() ->
    X = 3,
    <<A:X/binary, B/binary>> = <<"abcde">>,
    case is_binary(A) of
      true -> ok;
      false -> ok
    end,
    B.

-spec b3() -> binary().
b3() ->
    X = 3,
    case <<"abcde">> of
        <<A:X/binary, B/binary>> ->
            case is_binary(A) of
              true -> ok;
              false -> ok
            end,
            B;
        _ -> <<>>
    end.

-spec b4_fail() -> binary().
b4_fail() ->
    X = not_int,
    <<_:X/binary, B/binary>> = <<"abcde">>,
    B.

-spec b5_embed_binary() -> binary().
b5_embed_binary() ->
  <<"abc">> = <<(<<"abc">>)/binary>>,
  <<"abc">>.


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

% Atom where binary expected in construction
-spec bin_type_error_05_fail(atom()) -> binary().
bin_type_error_05_fail(X) -> <<X>>.

% bitstring() is no subtype of binary()
-spec bin_subtype_01_fail() -> binary().
bin_subtype_01_fail() -> <<1:1>>.


% ============================================================
% === Matching
% ============================================================

-spec bin_match_int_02(binary()) -> integer().
bin_match_int_02(<<A, _/binary>>) -> A;
bin_match_int_02(<<>>) -> error(exhaustive).

-spec bin_match_int_02_fail(binary()) -> integer().
bin_match_int_02_fail(<<A, _/binary>>) -> A.

% Match head and tail
-spec bin_match_bin_02(binary()) -> {integer(), binary()}.
bin_match_bin_02(<<H, T/binary>>) -> {H, T};
bin_match_bin_02(<<>>) -> error(exhaustive).

-spec bin_match_literal_02(undefined | binary()) -> ok | error | other.
bin_match_literal_02(T) ->
    case T of
        undefined -> error;
        <<"ok">> -> ok;
        _ -> other
    end.

% Different two-byte prefixes (like the number_exponation_part example)
-spec bin_cons_03(binary()) -> a | b | c | other.
bin_cons_03(<<$e, $+, _/binary>>) -> a;
bin_cons_03(<<$e, $-, _/binary>>) -> b;
bin_cons_03(<<$E, _/binary>>) -> c;
bin_cons_03(_) -> other.

% Same leading byte: second clause is redundant
-spec bin_cons_02_fail(binary()) -> a | b | other.
bin_cons_02_fail(<<1, _/binary>>) -> a;
bin_cons_02_fail(<<1, _/binary>>) -> b;
bin_cons_02_fail(_) -> other.

% Different literal UTF-8 values should not be redundant
-spec bin_utf8_cons_01(binary()) -> a | b | other.
bin_utf8_cons_01(<<$a/utf8, _/binary>>) -> a;
bin_utf8_cons_01(<<$b/utf8, _/binary>>) -> b;
bin_utf8_cons_01(_) -> other.

-spec bin_utf8_var_01(binary()) -> char | empty | invalid.
bin_utf8_var_01(<<_/utf8, _/binary>>) -> char;
bin_utf8_var_01(<<>>) -> empty;
bin_utf8_var_01(_) -> invalid.

% not every binary starts with a character
-spec bin_utf8_var_01_fail(binary()) -> char | empty.
bin_utf8_var_01_fail(<<_/utf8, _/binary>>) -> char;
bin_utf8_var_01_fail(<<>>) -> empty.

% 256 does not fit: the first clause is dead
-spec bin_literal_range_01_fail(binary()) -> a | b.
bin_literal_range_01_fail(<<256>>) -> a;
bin_literal_range_01_fail(_) -> b.

-spec bin_unit_01(<<_:_*16>>) -> ok.
bin_unit_01(<<_/binary-unit:16>>) -> ok.

-spec bin_unit_01_fail(binary()) -> ok.
bin_unit_01_fail(<<_/binary-unit:16>>) -> ok.

-spec bin_type_error_04_fail(binary()) -> non_neg_integer().
bin_type_error_04_fail(B) ->
    <<A/signed>> = B,
    A.

-spec bin_let_01(binary()) -> {integer(), integer()}.
bin_let_01(Bin) ->
    <<A, B, _/binary>> = ?assert_pattern(<<_, _, _/binary>>, Bin),
    {A, B}.

% Bind variables from binary match
-spec bin_let_01_fail(binary()) -> {integer(), integer()}.
bin_let_01_fail(Bin) ->
    <<A, B, _/binary>> = Bin,
    {A, B}.


% ============================================================
% === Values and sizes known at run time only
% ============================================================

-spec bin_run_time_03(binary()) -> binary() | none.
bin_run_time_03(<<L, P:L/binary, _/binary>>) -> P;
bin_run_time_03(_) -> none.

% the first byte need not be X
-spec bin_run_time_04_fail(byte(), nonempty_binary()) -> same.
bin_run_time_04_fail(X, <<X, _/binary>>) -> same.


% ============================================================
% === Guards
% ============================================================

-spec bin_seg_guard_01(binary()) -> digit | other | empty.
bin_seg_guard_01(<<C, _/binary>>) when C >= $0, C =< $9 -> digit;
bin_seg_guard_01(<<_, _/binary>>) -> other;
bin_seg_guard_01(<<>>) -> empty.

% the guard does not cover every byte
-spec bin_seg_guard_01_fail(binary()) -> digit | empty.
bin_seg_guard_01_fail(<<C, _/binary>>) when C >= $0, C =< $9 -> digit;
bin_seg_guard_01_fail(<<>>) -> empty.

-spec bin_guard_03_fail(integer() | binary()) -> integer().
bin_guard_03_fail(I) when is_binary(I), size(I) > 3 -> 3;
bin_guard_03_fail(I) -> I.

% Guard comparing to literal binary
-spec bin_guard_literal_01(binary()) -> ok | error.
bin_guard_literal_01(V) when V =:= <<"ok">> -> ok;
bin_guard_literal_01(_) -> error.

% a guard on the size says nothing about the bitstring
-spec bin_size_guard_02(binary(), integer()) -> big | small.
bin_size_guard_02(X, N) when byte_size(X) > N -> big;
bin_size_guard_02(_, _) -> small.

-spec bin_size_guard_02_fail(binary(), integer()) -> ok.
bin_size_guard_02_fail(X, N) when byte_size(X) > N -> ok.

% byte_size(X) on an atom only makes the guard fail
-spec bin_size_guard_04(binary() | atom(), integer()) -> binary() | other.
bin_size_guard_04(X, N) when byte_size(X) > N -> X;
bin_size_guard_04(_, _) -> other.

% A bitstring cell holds one bit and a bitstring, so the kinds of terms cover term()
-spec bin_kinds_01(term()) -> ok.
bin_kinds_01(X) when is_atom(X) -> ok;
bin_kinds_01(X) when is_number(X) -> ok;
bin_kinds_01(X) when is_bitstring(X) -> ok;
bin_kinds_01(X) when is_list(X) -> ok;
bin_kinds_01(X) when is_tuple(X) -> ok;
bin_kinds_01(X) when is_map(X) -> ok;
bin_kinds_01(X) when is_function(X) -> ok;
bin_kinds_01(X) when is_pid(X) -> ok;
bin_kinds_01(X) when is_port(X) -> ok;
bin_kinds_01(X) when is_reference(X) -> ok.


% ============================================================
% === Precision the checker does not have (ignored in tycheck_simple_tests)
% ============================================================

% TODO: integer segment variables get non_neg_integer() instead of the precise
% value from the scrutiny. To fix, the solver would need to project singleton
% bits back into integer values.
-spec bin_let_04() -> {1, 2, 3}.
bin_let_04() ->
    Bin = <<1, 2, 3>>,
    <<A, Rest1/binary>> = Bin,
    <<B, Rest2/binary>> = Rest1,
    <<C>> = Rest2,
    {A, B, C}.

% the bits of 1.0: the second clause is dead
-spec bin_float_exact_05_fail(<<_:32>>) -> one | other.
bin_float_exact_05_fail(<<1.0:32/float>>) -> one;
bin_float_exact_05_fail(<<16#3F, 16#80, 0, 0>>) -> other;
bin_float_exact_05_fail(_) -> other.

% <<1:16/little>> is <<1, 0>>: the second clause is dead
-spec bin_little_01_fail(binary()) -> one | other.
bin_little_01_fail(<<1:16/little, _/binary>>) -> one;
bin_little_01_fail(<<1, 0, _/binary>>) -> other;
bin_little_01_fail(_) -> other.

% the two guards cover every byte
-spec bin_seg_guard_02(binary()) -> low | high | empty.
bin_seg_guard_02(<<C, _/binary>>) when C < 128 -> low;
bin_seg_guard_02(<<C, _/binary>>) when C >= 128 -> high;
bin_seg_guard_02(<<>>) -> empty.

-spec bin_exp_05() -> ok.
bin_exp_05() -> case <<16#E4/utf8>> of <<16#C3, 16#A4>> -> ok end.

-spec bin_seg_02(binary()) -> 0..15 | none.
bin_seg_02(<<A:4, _:4, _/binary>>) -> A;
bin_seg_02(_) -> none.

-spec bin_exp_10(binary()) -> a.
bin_exp_10(B) ->
    case <<"a", B/binary>> of
        <<"a", _/binary>> -> a
    end.

