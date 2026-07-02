-module(map_even2).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

% From "Castagna et al, Polymorphic Functions with Set-Theoretic Types, Part 1"

-spec my_map_infer(fun((A) -> B), list(A)) -> list(B).
my_map_infer(_, []) -> [];
my_map_infer(F, [X | Xs]) -> [F(X) | my_map_infer(F, Xs)].

% In plain erlang, do not have negation in erlang's type language, so we simulate the type
% by a constrained type variable.
-spec even(integer()) -> boolean(); (T) -> T when T :: atom() | tuple().
even(X) when is_integer(X) and (X rem 2 == 0) -> true;
even(X) when is_integer(X) and (X rem 2 == 1) -> false;
even(X) -> X.

-spec map_even(list(integer())) -> list(boolean());
              (list(T)) -> list(T);
              (list(T)) -> list(T | boolean()).
map_even(L) -> my_map_infer(fun even/1, L).

my_test() ->
    ?assertEqual(true, even(6)),
    ?assertEqual(false, even(7)),
    ?assertEqual([2,3,4], my_map_infer(fun (X) -> X + 1 end, [1,2,3])),
    ?assertEqual([some_atom], map_even([some_atom])),
    ?assertEqual([false, true, false], map_even([1,2,3])),
    ?assertEqual([false, some_atom, true], map_even([1, some_atom, 2])).


