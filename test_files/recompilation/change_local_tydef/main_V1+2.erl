-module(main).

-export([main/0]).

-spec main() -> integer().
main() -> foo:foo_fun(1,2).
