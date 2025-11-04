-module(down).

-export([f/1]).

-spec f(dynamic()) -> integer().
f(X) -> X.
