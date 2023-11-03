-module(test_inf).

-export([
    inc/1,
    foo/1,
    bar/0
]).

-spec inc(integer()) -> integer().
inc(X) -> X + 1.

%-spec foo(integer()) -> integer().
foo(X) -> inc(X).

-spec bar() -> integer().
bar() -> foo(42).
