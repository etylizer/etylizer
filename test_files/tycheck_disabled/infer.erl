-module(infer).

% Fails with (#68)
% escript: exception error: no match of right hand side value false
%   in function  etally:'-tally/2-lc$^6/1-1-'/2 (/Users/swehr/devel/etylizer/src/erlang_types/etally.erl, line 53)
%   in call from etally:tally/2 (/Users/swehr/devel/etylizer/src/erlang_types/etally.erl, line 53)
%   in call from tally:tally/4 (/Users/swehr/devel/etylizer/src/tally.erl, line 31)
%   in call from utils:timing/1 (/Users/swehr/devel/etylizer/src/utils.erl, line 310)
%   in call from typing:'-infer/2-fun-5-'/5 (/Users/swehr/devel/etylizer/src/typing.erl, line 203)
%   in call from lists:flatmap_1/2 (lists.erl, line 1335)
%   in call from lists:flatmap_1/2 (lists.erl, line 1335)
%   in call from typing:infer/2 (/Users/swehr/devel/etylizer/src/typing.erl, line 197)

-export([bar/0, foo/0]).

% Type of map should be inferred
myMap([], _) -> [];
myMap([X | XS], F) -> [F(X) | myMap(XS, F)].

-spec foo() -> list(integer()).
foo() -> myMap(["Hello", "World"], fun(X) -> "XX" ++ X ++ "ZZ" end).

-spec bar() -> list(integer()).
bar() -> myMap([1,2,3], fun(X) -> X + 1 end).
