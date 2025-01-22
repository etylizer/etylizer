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
