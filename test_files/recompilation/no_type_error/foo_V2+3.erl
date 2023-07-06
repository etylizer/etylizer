-module(foo).

-export([foo/1]).

-spec bar(integer()) -> integer().
bar(X) -> X.

% foo fails to type check
-spec foo(integer()) -> integer().
foo(X) -> bar(X).
