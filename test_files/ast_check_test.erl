-module(ast_check_test).

-export([bar/1, foo/0]).

-spec bar([integer()]) -> integer().
bar(_L) -> 1.

foo() ->
    try bar([])
    catch
        {a,X} when false -> X
    end.
