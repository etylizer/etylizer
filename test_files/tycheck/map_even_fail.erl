-module(map_even_fail).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

% From "Castagna et al, Polymorphic Functions with Set-Theoretic Types, Part 1"

-spec my_map_infer(fun((A) -> B), list(A)) -> list(B).
my_map_infer(_, []) -> [];
my_map_infer(F, [X | Xs]) -> [F(X) | my_map_infer(F, Xs)].

% We do not have negation in erlang's type language, so we simulate the type
% by a constrained type variable. We could add a "is not subtype of" constraint
% to encode that T might everything but not an integer.
% Idea for writing the "is not subtype of" constraint:
% when T :: not(integer()).
-spec even(integer()) -> boolean(); (T) -> T when T :: atom() | tuple().
even(X) when is_integer(X) and (X rem 2 == 0) -> true;
even(X) when is_integer(X) and (X rem 2 == 1) -> false;
even(X) -> X.

-spec map_even(list(integer())) -> list(boolean());
              (list(T)) -> list(T).
map_even(L) -> my_map_infer(fun even/1, L).

my_test() ->
    ?assertEqual([false, some_atom, true], map_even([1, some_atom, 2])).
