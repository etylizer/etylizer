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
