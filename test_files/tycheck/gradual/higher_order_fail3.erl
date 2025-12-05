% ERROR
% apply_fun(fun d2/1)

-module(higher_order).

-export([main/0]).

-spec apply_fun(fun((integer()) -> atom())) -> atom().
apply_fun(F) -> F(42).

-spec f(integer()) -> atom().
f(_) -> f.

-spec d1(dynamic()) -> dynamic().
d1(X) -> X.

-spec d2(dynamic()) -> string().
d2(X) -> X.

-spec d3(integer()) -> dynamic().
d3(X) -> X.

-spec is_atom_list(list(atom())) ->  ok.
is_atom_list(_) -> ok.

-spec main() -> ok.
main() ->
    A1 = apply_fun(fun(_X) -> false end),
    A2 = apply_fun(fun f/1),
    A3 = apply_fun(fun d1/1),
    A4 = apply_fun(fun d2/1),
    A5 = apply_fun(fun d3/1),
    is_atom_list([A1, A2, A3, A4, A5]).
