-module(foo).

-export([foo/1]).

-spec foo(boolean()) -> boolean().
foo(X) -> X.
