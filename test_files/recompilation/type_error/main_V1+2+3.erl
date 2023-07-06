-module(main).

-export([main/0]).

-spec main() -> integer().
main() -> foo:foo(1).
