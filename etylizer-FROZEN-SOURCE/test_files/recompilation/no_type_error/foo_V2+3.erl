-module(foo).

-export([foo/1]).

-spec bar(boolean()) -> boolean().
bar(X) -> X.

% foo fails to type check
-spec foo(boolean()) -> boolean().
foo(X) -> bar(X).
