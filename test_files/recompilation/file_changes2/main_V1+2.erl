-module(main).

-export([main/0]).
-import(foo, [foo_fun/2]).

-spec main() -> integer().
main() -> foo_fun(1,2).
