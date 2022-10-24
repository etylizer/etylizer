-module(test_inf_fail).

-export([
    inc/1,
    foo/1,
    bar/0
]).

-spec inc(integer()) -> integer().
inc(X) -> X + 1.

%-spec foo(integer()) -> integer().
foo(X) -> inc(X).

% should fail because the inferred type for foo is integer() -> integer()
-spec bar() -> integer().
bar() -> foo("xxx").
