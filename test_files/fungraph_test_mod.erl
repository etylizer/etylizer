-module(fungraph_test_mod).

-export([buzz/0]).

% This module has the following function dependency graph:
% {spam}, {foo, bar, with_spec}, {egg}, {buzz}

spam() -> 42.

-spec with_spec() -> integer().
with_spec() -> foo().

bar() -> with_spec().

foo() -> spam() + bar().

egg(L) -> lists:map(fun foo/0, L).

buzz() -> egg([1,2,3]).
