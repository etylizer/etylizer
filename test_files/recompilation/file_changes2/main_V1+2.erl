-module(main).

-export([main/0]).
-import(foo, [foo_fun/2]).

-spec main() -> boolean().
main() -> foo_fun(true,false).
