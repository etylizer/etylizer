-module(ast_check_test).

-export([bar/1, foo/0, baz/2]).

-spec bar([integer()]) -> integer().
bar(_L) -> 1.

foo() ->
    try bar([])
    catch
        {a,X} when false -> X
    end.

baz(M, A) -> fun M:bar/A.
