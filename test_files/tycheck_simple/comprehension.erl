-module(comprehension).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

% strict and non-strict versions;
% strict only behaves differently when the pattern match fails
%   i.e. the pattern match should be the same as the element type of the input list

-spec lc_01() -> [integer()].
lc_01() -> [I || I <- [1,2]].

-spec lc_01s() -> [integer()].
lc_01s() -> [I || I <:- [1,2]].

-spec lc_02_fail() -> [integer()].
lc_02_fail() -> [I || I <- [1,foo]]. % fails because pattern I does not filter foo

-spec lc_02s_fail() -> [integer()].
lc_02s_fail() -> [I || I <:- [1,foo]]. 

-spec lc_03([integer()]) -> [integer()].
lc_03(L) -> [I || I <- L].

-spec lc_03s([integer()]) -> [integer()].
lc_03s(L) -> [I || I <:- L].

-spec lc_04([integer()]) -> [integer()].
lc_04(L) -> [I + J || I <- L, J <- L].

-spec lc_05_fail([integer()], [string()]) -> [integer()].
lc_05_fail(L, Z) -> [I + J || I <- L, J <- Z].

% we can't statically verify that the result is just []
-spec lc_06() -> [ok].
lc_06() -> [ok || _ <- []].

-spec lc_07_fail() -> [].
lc_07_fail() -> [ok || _ <- []].

-spec lc_08() -> [integer()].
lc_08() -> [I || I <- [1], true].

-spec lc_09() -> [integer()].
lc_09() -> 
  [1 || X <- [42], X > 3].

% cartesian product example from Erlang documentation
-spec lc_10() -> [{integer(), atom()}].
lc_10() -> 
  [{X, Y} || X <- [1,2,3], Y <- [a,b]].

% test for a scoping bug
-spec lc_11(list(boolean())) -> list({boolean(), boolean()}).
lc_11(Alts) -> [{S, A} || A <- Alts, S=A].

% filter expression result (S=A) must be boolean
-spec lc_12_fail(list(T)) -> list({T, T}).
lc_12_fail(Alts) -> [{S, A} || A <- Alts, S=A].

-spec lc_13_fail() -> [integer()].
lc_13_fail() -> 
  [X || X <- [1,a,2,b,3], X > 3].

-spec lc_13b() -> [integer()].
lc_13b() -> 
  [X || X <- [1,a,2,b,3], is_integer(X)].

-spec lc_14(list(boolean())) -> list(boolean()).
lc_14(Alts) -> [S || A <- Alts, case A of S -> S end].

-spec lc_15([{fun_full, [A], B} | {other_type}]) -> [{A, B}].
lc_15(Funs) -> [{A, B} || {fun_full, [A], B} <- Funs].

-spec lc_15s_fail([{fun_full, [A], B} | {other_type}]) -> [{A, B}].
lc_15s_fail(Funs) -> [{A, B} || {fun_full, [A], B} <:- Funs].

-spec lc_16([{f, a} | b]) -> [a].
lc_16(Funs) -> [A || {f, A} <- Funs].

% strict list generator with constant pattern
-spec lc_17_fail([atom()]) -> [ok].
lc_17_fail(L) ->
  [ok || ok <:- L].

-spec mc_01() -> #{atom() => integer()}.
mc_01() -> 
  #{K => V || {K, V} <- [{hello, 42}]}.

-spec mc_02_fail() -> #{atom() => integer()}.
mc_02_fail() -> 
  #{K => V || {K, V} <- [{hello, ok}]}.

-spec mc_03() -> #{atom() => atom()}.
mc_03() -> 
  #{K => V || K := V <- #{foo => bar}}.

-spec mc_04(#{atom() => atom()}) -> #{atom() => ok}.
mc_04(M) -> 
  #{K => ok || K := ok <- M}.

-spec mc_05_fail(#{atom() => atom()}) -> #{atom() => ok}.
mc_05_fail(M) ->
  #{K => ok || K := ok <:- M}. % strictness causes exception

-spec zip_01() -> [{integer(), atom(), integer()}].
zip_01() ->
  [{X, Y, Z} || X <- [1,2,3] && Y <- [a,b,c], Z <- [1,2,3]].

-spec zip_02_fail() -> [{integer(), atom()}].
zip_02_fail() ->
  [{X, Y} || X <- [1] && Y <- [4]].

% #20
-spec lc_15_fail(integer()) -> list().
lc_15_fail(N) ->  [X || X <- N].

