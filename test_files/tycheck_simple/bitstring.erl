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
% === Binary construction - integer segments
% ============================================================

% Construct a single-byte binary with literal integer
-spec bin_construct_int_01() -> binary().
bin_construct_int_01() -> <<42>>.

% Construct a multi-byte binary with literal integers
-spec bin_construct_int_02() -> binary().
bin_construct_int_02() -> <<1, 2, 3>>.

% Construct a binary from a variable (default 8-bit integer)
-spec bin_construct_int_03(integer()) -> binary().
bin_construct_int_03(X) -> <<X>>.

% Construct a binary with explicit 16-bit size
-spec bin_construct_int_04(integer()) -> binary().
bin_construct_int_04(X) -> <<X:16>>.

% Construct a binary with explicit 32-bit integer type specifier
-spec bin_construct_int_05(integer()) -> binary().
bin_construct_int_05(X) -> <<X:32/integer>>.

% Construct a bitstring (3 bits, not byte-aligned)
-spec bin_construct_int_06(integer()) -> bitstring().
bin_construct_int_06(X) -> <<X:3>>.

% Construct with little-endian
-spec bin_construct_int_07() -> binary().
bin_construct_int_07() -> <<16#1234:16/little>>.

% Construct from two variables
-spec bin_construct_int_08(integer(), integer()) -> binary().
bin_construct_int_08(A, B) -> <<A, B>>.

% Construct with variable size
-spec bin_construct_int_09(integer(), integer()) -> bitstring().
bin_construct_int_09(X, Size) -> <<X:Size>>.


% ============================================================
% === Binary construction - float segments
% ============================================================

% Construct with default float (64-bit)
-spec bin_construct_float_01(float()) -> binary().
bin_construct_float_01(X) -> <<X/float>>.

% Construct with 32-bit float
-spec bin_construct_float_02(float()) -> binary().
bin_construct_float_02(X) -> <<X:32/float>>.

% Construct with 32-bit little-endian float (from Gradualizer bitstring.erl)
-spec bin_construct_float_03(float()) -> binary().
bin_construct_float_03(A) -> <<A:32/float-little>>.


% ============================================================
% === Binary construction - binary/bitstring segments
% ============================================================

% Concatenate two binaries
-spec bin_construct_bin_01(binary(), binary()) -> binary().
bin_construct_bin_01(A, B) -> <<A/binary, B/binary>>.

% Embed a bitstring segment
-spec bin_construct_bin_02(bitstring()) -> bitstring().
bin_construct_bin_02(A) -> <<A/bitstring>>.

% String literal construction
-spec bin_construct_str_01() -> binary().
bin_construct_str_01() -> <<"hello">>.

% Sized binary segment
-spec bin_construct_bin_03(binary()) -> binary().
bin_construct_bin_03(A) -> <<A:3/binary>>.

% Complex construction with multiple specifiers (from Gradualizer bitstring.erl)
-spec bin_construct_complex_01() -> bitstring().
bin_construct_complex_01() ->
    <<"abc", 42, "abc"/utf32, "abc"/float, 42/float-little,
      (<<"abc">>):8/bits, (<<"abc">>)/bytes>>.


% ============================================================
% === Binary construction - UTF segments
% ============================================================

% UTF-8 encoded character
-spec bin_construct_utf8_01() -> binary().
bin_construct_utf8_01() -> <<1024/utf8>>.

% UTF-16 encoded character
-spec bin_construct_utf16_01() -> binary().
bin_construct_utf16_01() -> <<1024/utf16>>.

% UTF-32 encoded character
-spec bin_construct_utf32_01() -> binary().
bin_construct_utf32_01() -> <<1024/utf32>>.

% UTF-8 string literal sugar
-spec bin_construct_utf8_02() -> binary().
bin_construct_utf8_02() -> <<"abc"/utf8>>.

% UTF-16 with endianness
-spec bin_construct_utf16_02() -> binary().
bin_construct_utf16_02() -> <<"xyz"/utf16-little>>.


% ============================================================
% === Binary construction - unit-based (from Gradualizer)
% ============================================================

% Unit-based construction: result is multiple of 6 bits
-spec bin_construct_unit_01(integer(), integer()) -> <<_:_*6>>.
bin_construct_unit_01(A, B) ->
    <<0:A/integer-unit:36, 1:B/integer-unit:30>>.


% ============================================================
% === Binary construction - fixed-size results
% ============================================================

% IPv4 address to 32-bit binary (from Gradualizer bc_pass.erl)
-spec bin_construct_fixed_01({byte(), byte(), byte(), byte()}) -> <<_:32>>.
bin_construct_fixed_01({A, B, C, D}) ->
    <<A, B, C, D>>.

% 128-bit binary
-spec bin_construct_fixed_02() -> binary().
bin_construct_fixed_02() -> <<128>>.

% 16-bit binary from two bytes
-spec bin_construct_fixed_03() -> binary().
bin_construct_fixed_03() -> <<16#12, 16#34>>.


% ============================================================
% === Binary pattern matching - integer segments
% ============================================================

% Match and extract nibbles (from Gradualizer bitstring.erl)
-spec bin_match_int_01(binary()) -> integer().
bin_match_int_01(<<A:4, B:4, _/binary>>) ->
    A + B.

% Match first byte
-spec bin_match_int_02(binary()) -> integer().
bin_match_int_02(<<A, _/binary>>) -> A.

% Match two bytes and return their sum
-spec bin_match_int_03(binary()) -> integer().
bin_match_int_03(<<A, B, _/binary>>) -> A + B.

% Match with explicit integer type
-spec bin_match_int_04(binary()) -> integer().
bin_match_int_04(<<A:16/integer, _/binary>>) -> A.

% Match with little-endian
-spec bin_match_int_05(binary()) -> integer().
bin_match_int_05(<<A:16/little, _/binary>>) -> A.

% Match signed integer
-spec bin_match_int_06(binary()) -> integer().
bin_match_int_06(<<A:8/signed, _/binary>>) -> A.

% Match unsigned integer (default)
-spec bin_match_int_07(binary()) -> non_neg_integer().
bin_match_int_07(<<A:8/unsigned, _/binary>>) -> A.


% ============================================================
% === Binary pattern matching - float segments
% ============================================================

% Match a 64-bit float
-spec bin_match_float_01(binary()) -> float().
bin_match_float_01(<<F:64/float, _/binary>>) -> F.

% Match a 32-bit float
-spec bin_match_float_02(binary()) -> float().
bin_match_float_02(<<F:32/float, _/binary>>) -> F.


% ============================================================
% === Binary pattern matching - binary segments
% ============================================================

% Match binary with rest
-spec bin_match_bin_01(binary()) -> binary().
bin_match_bin_01(<<_:8, Rest/binary>>) -> Rest.

% Match head and tail
-spec bin_match_bin_02(binary()) -> {integer(), binary()}.
bin_match_bin_02(<<H, T/binary>>) -> {H, T}.

% Match with variable size (from existing b3)
-spec bin_match_bin_03(binary(), non_neg_integer()) -> binary().
bin_match_bin_03(Bin, Size) ->
    <<_:Size/binary, Rest/binary>> = Bin,
    Rest.


% ============================================================
% === Binary pattern matching - exhaustiveness
% ============================================================

% Exhaustive binary matching: empty or at least one byte
% (from Gradualizer binary_exhaustiveness_checking.erl)
-spec bin_exhaust_01(binary()) -> ok.
bin_exhaust_01(<<>>) -> ok;
bin_exhaust_01(<<_:8, _/binary>>) -> ok.

% Same with reversed clause order
-spec bin_exhaust_02(binary()) -> ok.
bin_exhaust_02(<<_:8, _/binary>>) -> ok;
bin_exhaust_02(<<>>) -> ok.

% Split byte into nibbles (from Gradualizer)
-spec bin_exhaust_03(binary()) -> ok.
bin_exhaust_03(<<_:4, _:4, _/binary>>) -> ok.

% Recursive binary traversal
-spec bin_exhaust_04(binary()) -> non_neg_integer().
bin_exhaust_04(<<>>) -> 0;
bin_exhaust_04(<<_, Rest/binary>>) -> 1 + bin_exhaust_04(Rest).


% ============================================================
% === Binary pattern matching - literal patterns
% ============================================================

% Match literal binary string
-spec bin_match_literal_01(binary()) -> ok | error.
bin_match_literal_01(<<"ok">>) -> ok;
bin_match_literal_01(_) -> error.

% Literal binary in case expression
% (from Gradualizer binary_literal_pattern.erl)
-spec bin_match_literal_02(undefined | binary()) -> ok | error | other.
bin_match_literal_02(T) ->
    case T of
        undefined -> error;
        <<"ok">> -> ok;
        _ -> other
    end.

% Match specific byte values
-spec bin_match_literal_03(binary()) -> a | b | other.
bin_match_literal_03(<<0, _/binary>>) -> a;
bin_match_literal_03(<<1, _/binary>>) -> b;
bin_match_literal_03(_) -> other.


% ============================================================
% === Binary guards - is_binary / is_bitstring
% ============================================================

% Guard with is_binary (from Gradualizer guard.erl)
-spec bin_guard_01(binary() | atom()) -> binary() | not_binary.
bin_guard_01(B) when is_binary(B) -> B;
bin_guard_01(_) -> not_binary.

% Guard with is_bitstring
-spec bin_guard_02(bitstring() | atom()) -> bitstring() | not_bitstring.
bin_guard_02(B) when is_bitstring(B) -> B;
bin_guard_02(_) -> not_bitstring.

% Guard chain: is_binary then size check
% (from Gradualizer guard.erl)
% this was wrongly categorized as pass
-spec bin_guard_03_fail(integer() | binary()) -> integer().
bin_guard_03_fail(I) when is_binary(I), size(I) > 3 -> 3;
bin_guard_03_fail(I) -> I.

% Negated binary guard: not is_binary
-spec bin_guard_04(atom() | integer() | binary()) -> binary().
bin_guard_04(A) when not is_binary(A) -> <<>>;
bin_guard_04(B) -> B.

% Guard with is_binary on two variables
% (from Gradualizer guard.erl)
-spec bin_guard_05(integer() | binary(), atom()) -> integer().
bin_guard_05(I, J) when is_binary(I), is_atom(J) -> 3;
bin_guard_05(I, _) -> I.


% ============================================================
% === Binary concatenation with guards
% (from eqwalizer eqwater.erl foo1-foo6)
% ============================================================

% Concatenate or return empty depending on guard
-spec bin_concat_01({atom() | binary(), atom() | binary()}) -> binary().
bin_concat_01({X, Y}) when is_atom(X) or is_atom(Y) -> <<>>;
bin_concat_01({B1, B2}) -> <<B1/binary, B2/binary>>.

% Same with two separate args
-spec bin_concat_02(atom() | binary(), atom() | binary()) -> binary().
bin_concat_02(X, Y) when is_atom(X) or is_atom(Y) -> <<>>;
bin_concat_02(B1, B2) -> <<B1/binary, B2/binary>>.

% Negated atom guards
-spec bin_concat_03({atom() | binary(), atom() | binary()}) -> binary().
bin_concat_03({B1, B2}) when (not is_atom(B1)) and (not is_atom(B2)) ->
    <<B1/binary, B2/binary>>;
bin_concat_03({_, _}) -> <<>>.

% Multiple guard clauses for binary concat
-spec bin_concat_04({atom() | binary(), atom() | binary()}) -> binary().
bin_concat_04({A1, A2}) when is_atom(A1) and is_atom(A2) -> <<>>;
bin_concat_04({A, B}) when is_atom(A) -> B;
bin_concat_04({B, A}) when is_atom(A) -> B;
bin_concat_04({B1, B2}) -> <<B1/binary, B2/binary>>.


% ============================================================
% === Binary pattern matching with occurrence typing
% (from eqwalizer eqwater.erl occ_binary_pat_*)
% ============================================================

% Binary size pattern refines type to binary()
-spec bin_occ_01(binary() | string(), integer()) -> binary().
bin_occ_01(X, Size) ->
    case X of
        <<_:Size/binary>> -> X;
        _ -> <<>>
    end.

% Binary pattern in tuple context
-spec bin_occ_02({binary(), binary()} | {atom(), atom()}, integer()) -> binary().
bin_occ_02(X, Size) ->
    case X of
        {<<_:Size/binary>>, Bin} -> Bin;
        _ -> <<>>
    end.


% ============================================================
% === Signed / unsigned integer extraction
% (from Gradualizer bc_pass.erl)
% ============================================================

% Default (unsigned) integer from binary
-spec bin_signed_01(binary()) -> non_neg_integer().
bin_signed_01(B) ->
    <<A>> = B,
    A.

% Explicit unsigned integer
-spec bin_signed_02(binary()) -> non_neg_integer().
bin_signed_02(B) ->
    <<A/unsigned>> = B,
    A.

% Signed integer
-spec bin_signed_03(binary()) -> integer().
bin_signed_03(B) ->
    <<A/signed>> = B,
    A.

% Expression vs pattern default: constructing with -1 but matching unsigned
-spec bin_signed_04() -> non_neg_integer().
bin_signed_04() ->
    <<A>> = <<-1>>,
    A.

% Expression vs pattern unsigned
-spec bin_signed_05() -> non_neg_integer().
bin_signed_05() ->
    <<A/unsigned>> = <<-1>>,
    A.

% Expression vs pattern signed
-spec bin_signed_06() -> integer().
bin_signed_06() ->
    <<A/signed>> = <<-1>>,
    A.


% ============================================================
% === Precise bitstring types
% ============================================================

% 32-bit binary from four bytes
-spec bin_precise_01() -> <<_:32>>.
bin_precise_01() -> <<1, 2, 3, 4>>.

% 32-bit binary from tuple
-spec bin_precise_02({byte(), byte(), byte(), byte()}) -> <<_:32>>.
bin_precise_02({A, B, C, D}) -> <<A, B, C, D>>.

% 16-bit fixed-size binary
-spec bin_precise_03() -> <<_:16>>.
bin_precise_03() -> <<"xy">>.

% Bitstring with fixed size plus unit multiple
% (from Gradualizer bc_pass.erl)
-spec bin_precise_04(integer()) -> <<_:17, _:_*3>>.
bin_precise_04(N) ->
    <<3:17, N:9>>.


% ============================================================
% === Binary comprehensions
% ============================================================

% Simple binary comprehension from list
-spec bin_comp_01() -> binary().
bin_comp_01() -> << <<X>> || X <- [1, 2, 3] >>.

% List comprehension with binary generator
-spec bin_comp_02() -> [integer()].
bin_comp_02() -> [X || <<X>> <= <<1, 2, 3>>].

% Binary comprehension with binary generator
-spec bin_comp_03() -> binary().
bin_comp_03() -> << <<X>> || <<X>> <= <<1, 2, 3>> >>.

% Binary comprehension with nibbles
% (from Gradualizer bc_pass.erl)
-spec bin_comp_04() -> binary().
bin_comp_04() ->
    << <<X:4, Y:4>> || X <- [$a, $b], <<Y:4>> <= <<"xy">> >>.

% Binary comprehension from binary input
% (from Gradualizer bc_pass.erl)
-spec bin_comp_05(binary()) -> binary().
bin_comp_05(Bin) ->
    << <<X:4, Y:4>> || X <- [1, 2], <<Y:4>> <= Bin >>.

% Binary comprehension: slice bytes
-spec bin_comp_06() -> binary().
bin_comp_06() ->
    << <<B:2/bytes>> || <<B:4/bytes>> <= <<"abcdefgh">> >>.


% ============================================================
% === Type subtyping: binary() vs bitstring()
% ============================================================

% binary() is a subtype of bitstring()
-spec bin_subtype_01() -> bitstring().
bin_subtype_01() -> <<"hello">>.

% bitstring() is NOT a subtype of binary() - should fail
-spec bin_subtype_01_fail() -> binary().
bin_subtype_01_fail() -> <<1:1>>.

% Empty binary is both binary() and bitstring()
-spec bin_subtype_02() -> bitstring().
bin_subtype_02() -> <<>>.


% ============================================================
% === Failure cases - type mismatches
% ============================================================

% Integer spec but binary pattern (from Gradualizer bin_type_error.erl)
-spec bin_type_error_01_fail(integer()) -> ok.
bin_type_error_01_fail(<<>>) -> ok.

% Return binary where integer expected
-spec bin_type_error_02_fail(binary()) -> integer().
bin_type_error_02_fail(X) -> X.

% Return integer where binary expected
-spec bin_type_error_03_fail(integer()) -> binary().
bin_type_error_03_fail(X) -> X.

% Signed integer cannot be non_neg_integer
% (from Gradualizer bc_fail.erl)
-spec bin_type_error_04_fail(binary()) -> non_neg_integer().
bin_type_error_04_fail(B) ->
    <<A/signed>> = B,
    A.

% Atom where binary expected in construction
-spec bin_type_error_05_fail(atom()) -> binary().
bin_type_error_05_fail(X) -> <<X>>.


% ============================================================
% === Binary operations with try/catch
% ============================================================

% Binary result from catch
-spec bin_try_01(binary() | atom()) -> binary().
bin_try_01(X) ->
    try X of
        B when is_binary(B) -> B;
        _ -> <<>>
    catch
        _:_ -> <<>>
    end.


% ============================================================
% === Binary in function arguments
% ============================================================

% Pass binary to helper and get integer back
-spec bin_fun_01(binary()) -> integer().
bin_fun_01(Bin) ->
    bin_fun_01_helper(Bin).

-spec bin_fun_01_helper(binary()) -> integer().
bin_fun_01_helper(<<A, _/binary>>) -> A;
bin_fun_01_helper(<<>>) -> 0.

% Higher-order: apply function to binary
-spec bin_fun_02(fun((binary()) -> integer()), binary()) -> integer().
bin_fun_02(F, Bin) -> F(Bin).


% ============================================================
% === Binary in data structures
% ============================================================

% List of binaries
-spec bin_data_01() -> [binary()].
bin_data_01() -> [<<1>>, <<2>>, <<3>>].

% Tuple with binary
-spec bin_data_02() -> {binary(), integer()}.
bin_data_02() -> {<<"hello">>, 42}.

% Map with binary keys and values
-spec bin_data_03() -> #{binary() => integer()}.
bin_data_03() -> #{<<"a">> => 1, <<"b">> => 2}.


% ============================================================
% === Binary matching in let bindings
% ============================================================

% Bind variables from binary match
-spec bin_let_01(binary()) -> {integer(), integer()}.
bin_let_01(Bin) ->
    <<A, B, _/binary>> = Bin,
    {A, B}.

% Nested binary match
-spec bin_let_02(binary()) -> {integer(), binary()}.
bin_let_02(Bin) ->
    <<Len, Rest/binary>> = Bin,
    <<Payload:Len/binary, _/binary>> = Rest,
    {Len, Payload}.

% Multiple sequential matches
-spec bin_let_03() -> {integer(), integer(), integer()}.
bin_let_03() ->
    Bin = <<1, 2, 3>>,
    <<A, Rest1/binary>> = Bin,
    <<B, Rest2/binary>> = Rest1,
    <<C>> = Rest2,
    {A, B, C}.


% ============================================================
% === Recursive binary processing
% ============================================================

% Count bytes in binary
-spec bin_rec_01(binary()) -> non_neg_integer().
bin_rec_01(<<>>) -> 0;
bin_rec_01(<<_, Rest/binary>>) -> 1 + bin_rec_01(Rest).

% Sum all bytes
-spec bin_rec_02(binary()) -> non_neg_integer().
bin_rec_02(<<>>) -> 0;
bin_rec_02(<<B, Rest/binary>>) -> B + bin_rec_02(Rest).

% Find a byte in binary
-spec bin_rec_03(binary(), integer()) -> boolean().
bin_rec_03(<<>>, _) -> false;
bin_rec_03(<<X, _/binary>>, X) -> true;
bin_rec_03(<<_, Rest/binary>>, X) -> bin_rec_03(Rest, X).

% Convert binary to list of integers
-spec bin_rec_04(binary()) -> [integer()].
bin_rec_04(<<>>) -> [];
bin_rec_04(<<B, Rest/binary>>) -> [B | bin_rec_04(Rest)].


% ============================================================
% === Guard expressions involving binary BIFs
% ============================================================

% byte_size guard
-spec bin_bif_guard_01(binary()) -> small | big.
bin_bif_guard_01(B) when byte_size(B) < 10 -> small;
bin_bif_guard_01(_) -> big.

% bit_size guard
-spec bin_bif_guard_02(bitstring()) -> small | big.
bin_bif_guard_02(B) when bit_size(B) < 80 -> small;
bin_bif_guard_02(_) -> big.


% ============================================================
% === Binary with case expressions
% ============================================================

% Case on binary content
-spec bin_case_01(binary()) -> atom().
bin_case_01(Bin) ->
    case Bin of
        <<"true">> -> true;
        <<"false">> -> false;
        <<>> -> empty;
        _ -> other
    end.

% Case with binary pattern and extraction
-spec bin_case_02(binary()) -> {ok, integer()} | empty.
bin_case_02(Bin) ->
    case Bin of
        <<H, _/binary>> -> {ok, H};
        <<>> -> empty
    end.


% ============================================================
% === Guard with binary literal comparison
% (from eqwalizer eqwater.erl occ_guard_binary_*)
% ============================================================

% Guard comparing to literal binary
-spec bin_guard_literal_01(binary()) -> ok | error.
bin_guard_literal_01(V) when V =:= <<"ok">> -> ok;
bin_guard_literal_01(_) -> error.

% Guard with not-equal to literal binary
-spec bin_guard_literal_02(binary()) -> binary().
bin_guard_literal_02(V) when V =/= <<"ok">> -> V;
bin_guard_literal_02(_) -> <<"matched_ok">>.


% ============================================================
% === Binary with andalso/orelse in guards
% (from eqwalizer eqwater.erl)
% ============================================================

% see #312
-spec bin_guard_andalso_01_fail(binary() | err) -> binary().
bin_guard_andalso_01_fail(V) ->
    is_atom(V) andalso throw(error),
    V.

% orelse guards for binary union
-spec bin_guard_orelse_01(atom() | integer() | binary()) -> binary().
bin_guard_orelse_01(A) when is_atom(A) orelse is_integer(A) -> <<>>;
bin_guard_orelse_01(B) -> B.

% Semicolon guards (same as orelse)
-spec bin_guard_semi_01(atom() | integer() | binary()) -> binary().
bin_guard_semi_01(A) when is_atom(A); is_integer(A) -> <<>>;
bin_guard_semi_01(B) -> B.
