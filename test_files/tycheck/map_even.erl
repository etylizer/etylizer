-module(map_even).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

%-opaque negation(T) :: ...
%-opaque intersection(T, U) :: ...
%-opaque without(T, U) :: intersection(T, negation(U)).

% From "Castagna et al, Polymorphic Functions with Set-Theoretic Types, Part 1"

-spec my_map_infer(fun((A) -> B), list(A)) -> list(B).
my_map_infer(_, []) -> [];
my_map_infer(F, [X | Xs]) -> [F(X) | my_map_infer(F, Xs)].

-spec even(integer()) -> boolean(); (T) -> T when T :: ety:negation(integer()).
even(X) when is_integer(X) and (X rem 2 == 0) -> true;
even(X) when is_integer(X) and (X rem 2 == 1) -> false;
even(X) -> X.

-spec map_even(list(integer())) -> list(boolean());
              (list(ety:negation(T, integer()))) -> list(ety:negation(T, integer()));
              (list(T | integer())) -> list(ety:negation(T, integer()) | boolean()).
map_even(L) -> my_map_infer(fun even/1, L).

my_test() ->
    ?assertEqual(true, even(6)),
    ?assertEqual(false, even(7)),
    ?assertEqual([2,3,4], my_map_infer(fun (X) -> X + 1 end, [1,2,3])),
    ?assertEqual([some_atom], map_even([some_atom])),
    ?assertEqual([false, true, false], map_even([1,2,3])),
    ?assertEqual([false, some_atom, true], map_even([1, some_atom, 2])).


