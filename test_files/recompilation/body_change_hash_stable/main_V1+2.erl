-module(main).

-export([main/0]).

-spec main() -> integer().
main() -> foo:f2() + bar:b1().
