-module(foo).

-export([foo/1]).

-spec bar(string()) -> string().
bar(X) -> X.

% foo fails to type check
-spec foo(boolean()) -> boolean().
foo(X) -> bar(X).
