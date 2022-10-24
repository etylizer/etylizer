-module(rep_ints).

-import(stdtypes, [tunion/1, tnegate/1, trange/2]).

-export([union/2, intersect/2, diff/2, negate/1]).
-export([empty/0, any/0]).
-export([interval/2, cointerval/2]).
-export([is_empty/1]).

-export([eval/1]).

%% intervals
%% representation
%% left? range* right?

empty() -> [].
any() -> [any_int].


eval([]) -> {predef, none};
eval(Ints) ->
    tunion(lists:map(
        fun
            (any_int) -> {predef, integer};
            ({left, To}) -> {range, '*', To};
            ({To, right}) -> {range, To, '*'};
            ({range, A, B}) -> {range, A, B}
        end, Ints)).

interval('*', '*') -> any();
interval('*', To) -> [{left, To}];
interval(From, '*') -> [{From, right}];
interval(From, To) when From =< To -> [{range, From, To}];
interval(_, _) -> [].

cointerval(From, To) ->
    negate(interval(From, To)).


is_empty([]) -> true;
is_empty(_) -> false.

negate([]) -> any();
negate([any_int]) -> empty();
negate([{left, X} | Xs]) -> negate_start_with(X + 1, Xs);
negate([{X, right} | _Xs]) -> [{left, X - 1}];
negate([{range, A, B} | Xs]) -> [{left, A - 1}] ++ negate_start_with(B + 1, Xs).

negate_start_with(Start, []) -> [{Start, right}];
negate_start_with(Start, [{range, A, B} | Xs]) -> [{range, Start, A-1}] ++ negate_start_with(B+1, Xs);
negate_start_with(Start, [{X, right} | _Xs]) -> [{range, Start, X - 1}].

union(I1, I2) ->
    lists:foldl(fun(I, Acc) -> interval_add(I, Acc) end, I1, I2).

intersect(I1, I2) ->
    negate(union(negate(I1), negate(I2))).

diff(I1, I2) ->
    intersect(I1, negate(I2)).


interval_add({range, A, B}, Xs) -> add_range(Xs, A, B);
interval_add({left, X}, Xs) -> add_left(Xs, X);
interval_add({X, right}, Xs) -> add_right(Xs, X);
interval_add(any_int, _Xs) -> any().


add_left([], B) -> [{left, B}];
add_left(All = [{range, A1, _} | _], B) when B < (A1 - 1) -> [{left, B}] ++ All;
add_left(All = [{A1, right} | _], B) when B < (A1 - 1) -> [{left, B}] ++ All;
add_left([{range, _, B1} | Xs], B) -> add_left(Xs, max(B, B1));
add_left(L = [{left, B1} | _], B) when B =< B1 -> L;
add_left([{left, _} | Xs], B) -> add_left(Xs, B);
add_left(_A, _B) ->
    any().

add_right([], A) -> [{A, right}];
add_right([I = {range, _, B1} | Xs], A) when (B1 + 1) < A -> [I] ++ add_right(Xs, A);
add_right([I = {left, B1} | Xs], A) when (B1 + 1) < A -> [I] ++ add_right(Xs, A);
add_right([{range, A1, _} | _], A) -> [{min(A, A1), right}];
add_right([{A1, right} | _], A) -> [{min(A, A1), right}];
add_right(_, _) -> any().

add_range([], A, B) -> [{range, A, B}];
add_range(L = [{range, A1, _} | _], A, B) when B < (A1 - 1) -> [{range, A, B}] ++ L;
add_range(L = [{A1, right} | _], A, B) when B < (A1 - 1) -> [{range, A, B}] ++ L;
add_range([I = {range, _, B1} | Xs], A, B) when (B1 + 1) < A -> [I] ++ add_range(Xs, A, B);
add_range([I = {left, B1} | Xs], A, B) when (B1 + 1) < A ->
    [I] ++ add_range(Xs, A, B);
add_range([{range, A1, B1} | Xs], A, B) -> add_range(Xs, min(A, A1), max(B, B1));
add_range([{left, B1} | Xs], _A, B) ->
    add_left(Xs, max(B, B1));
add_range([{A1, right} | _], A, _B) -> [{min(A, A1), right}];
add_range([any_int | _], _A, _B) -> any().
