-module(main).

-export([main/0]).

-spec main() -> boolean().
main() -> foo:foo_fun(true,false).
