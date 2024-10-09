-module(flatten).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

% Type for flatten from "Castagna, Programming with union, intersection, and negation types"
-type tree(T) :: etylizer:without(T, list()) | list(tree(T)).

% -spec flatten(tree(T)) -> list(etylizer:without(T, list())).
-spec flatten(tree(T)) -> list(T).
flatten([]) -> [];
flatten([H | T]) -> flatten(H) ++ flatten(T);
flatten(X) -> [X].

% Type for flatten from the erlang lib
-type deepList() :: [term() | deepList()].

-spec flatten_erl(deepList()) -> list().
flatten_erl([]) -> [];
flatten_erl([H | T]) -> flatten(H) ++ flatten(T);
flatten_erl(X) -> [X].

my_test() ->
    ?assertEqual([1,2,3,4,5], flatten([1, [2,3,[4, [5]]]])),
    ?assertEqual([1,2,3,4,5], flatten_erl([1, [2,3,[4, [5]]]])).
