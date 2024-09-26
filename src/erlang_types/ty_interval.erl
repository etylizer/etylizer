-module(ty_interval).

%% Efficient interval representation


-export([compare/2, equal/2]).


-export([empty/0, any/0]).
-export([union/2, intersect/2, diff/2, negate/1, is_any/1]).
-export([is_empty/1, eval/1, normalize/5, substitute/4, all_variables/2, to_singletons/1]).


-export([interval/2, cointerval/2]).
-export([transform/2, map_pi/1, has_ref/2]).

has_ref(_, _) -> false.

transform([], #{empty := E}) -> E();
transform([any_int], #{any := E}) -> E();
transform([Int | Others], Ops = #{union := U}) -> U([transform_single(Int, Ops), transform(Others, Ops)]).

transform_single({range, A, B}, #{to_int := Int}) -> Int(A, B);
% TODO hack
transform_single({left, -1}, _) -> {predef_alias, neg_integer};
transform_single({right, 1}, _) -> {predef_alias, pos_integer};

transform_single({left, L}, M = #{diff := D}) when L < -1 ->
    D({predef_alias, neg_integer}, transform_single({range, (L + 1), -1}, M));
transform_single({left, L}, M = #{union := U}) when L > -1 ->
    U([{predef_alias, neg_integer}, transform_single({range, -1, L}, M)]);

transform_single({right, R}, M = #{diff := D}) when R > 1 ->
    D({predef_alias, pos_integer}, transform_single({range, 1, (R - 1)}, M));
transform_single({right, R}, M = #{union := U}) when R < 1 ->
    U([{predef_alias, pos_integer}, transform_single({range, R, 1}, M)]).

to_singletons([]) -> [];
to_singletons([{range, A, B} | Ints]) ->
    [ty_rec:interval(dnf_var_int:int(interval(X, X))) || X <- lists:seq(A, B)] ++ to_singletons(Ints);
to_singletons(_) ->
    error(illegal_state).

%% representation
%% left? range* right?


% TODO witness
eval(_) -> erlang:error("TODO").

empty() -> [].
any() -> [any_int].

compare_int(I1, I2) when I1 =:= I2 -> 0;
compare_int(I1, I2) when I1 > I2 -> +1;
compare_int(I1, I2) when I1 < I2 -> -1.

compare([], []) -> +0;
compare([], _) -> -1;
compare(_, []) -> +1;
compare([{range, A1, _} | _], [{range, A2, _} | _]) when A1 /= A2 ->
    compare_int(A1, A2);
compare([{range, _, B1} | _], [{range, _, B2} | _]) when B1 /= B2 ->
    compare_int(B1, B2);
compare([{range, _, _} | Xs], [{range, _, _} | Ys]) ->
    compare(Xs, Ys);
compare([{range, _, _} | _], _) -> -1;
compare(_, [{range, _, _} | _]) -> +1;
compare([{left, A} | _], [{left, B} | _]) when A /= B ->
    compare_int(A, B);
compare([{left, _} | Xs], [{left, _} | Ys]) ->
    compare(Xs, Ys);
compare([{left, _} | _], _) -> -1; % sorted
compare(_, [{left, _} | _]) -> +1;
compare([{right, A} | _], [{right, B} | _]) when A /= B ->
    compare_int(A, B);
compare([{right, _} | Xs], [{right, _} | Ys]) ->
    compare(Xs, Ys);
compare([{right, _} | _], _) -> -1;
compare(_, [{right, _} | _]) -> +1;
compare([any_int], [any_int]) -> 0.

equal(I1, I2) -> compare(I1, I2) =:= 0.

interval('*', '*') -> any();
interval('*', To) -> [{left, To}];
interval(From, '*') -> [{right, From}];
interval(From, To) when From =< To -> [{range, From, To}];
interval(_, _) -> [].

cointerval(From, To) ->
    negate(interval(From, To)).

is_empty([]) -> true;
is_empty(_) -> false.

is_any([any_int]) -> true;
is_any(_) -> false.

negate([]) -> any();
negate([any_int]) -> empty();
negate([{left, X} | Xs]) -> negate_start_with(X + 1, Xs);
negate([{right, X} | _Xs]) -> [{left, X - 1}];
negate([{range, A, B} | Xs]) -> [{left, A - 1}] ++ negate_start_with(B + 1, Xs).

negate_start_with(Start, []) -> [{right, Start}];
negate_start_with(Start, [{range, A, B} | Xs]) -> [{range, Start, A-1}] ++ negate_start_with(B+1, Xs);
negate_start_with(Start, [{right, X} | _Xs]) -> [{range, Start, X - 1}].

union(I1, I2) ->
    lists:foldl(fun(I, Acc) -> interval_add(I, Acc) end, I1, I2).

intersect(I1, I2) ->
    negate(union(negate(I1), negate(I2))).

diff(I1, I2) ->
    intersect(I1, negate(I2)).

interval_add({range, A, B}, Xs) -> add_range(Xs, A, B);
interval_add({left, X}, Xs) -> add_left(Xs, X);
interval_add({right, X}, Xs) -> add_right(Xs, X);
interval_add(any_int, _Xs) -> any().

add_left([], B) -> [{left, B}];
add_left(All = [{range, A1, _} | _], B) when B < (A1 - 1) -> [{left, B}] ++ All;
add_left(All = [{right, A1} | _], B) when B < (A1 - 1) -> [{left, B}] ++ All;
add_left([{range, _, B1} | Xs], B) -> add_left(Xs, max(B, B1));
add_left(L = [{left, B1} | _], B) when B =< B1 -> L;
add_left([{left, _} | Xs], B) -> add_left(Xs, B);
add_left(_A, _B) ->
    any().

add_right([], A) -> [{right, A}];
add_right([I = {range, _, B1} | Xs], A) when (B1 + 1) < A -> [I] ++ add_right(Xs, A);
add_right([I = {left, B1} | Xs], A) when (B1 + 1) < A -> [I] ++ add_right(Xs, A);
add_right([{range, A1, _} | _], A) -> [{right, min(A, A1)}];
add_right([{right, A1} | _], A) -> [{right, min(A, A1)}];
add_right(_, _) -> any().

add_range([], A, B) -> [{range, A, B}];
add_range(L = [{range, A1, _} | _], A, B) when B < (A1 - 1) -> [{range, A, B}] ++ L;
add_range(L = [{right, A1} | _], A, B) when B < (A1 - 1) -> [{range, A, B}] ++ L;
add_range([I = {range, _, B1} | Xs], A, B) when (B1 + 1) < A -> [I] ++ add_range(Xs, A, B);
add_range([I = {left, B1} | Xs], A, B) when (B1 + 1) < A ->
    [I] ++ add_range(Xs, A, B);
add_range([{range, A1, B1} | Xs], A, B) -> add_range(Xs, min(A, A1), max(B, B1));
add_range([{left, B1} | Xs], _A, B) ->
    add_left(Xs, max(B, B1));
add_range([{right, A1} | _], A, _B) -> [{right, min(A, A1)}];
add_range([any_int | _], _A, _B) -> any().

normalize(TyInterval, [], [], _Fixed, _) ->
    % Fig. 3 Line 3
    case is_empty(TyInterval) of
        true -> [[]];
        false -> []
    end;
normalize(TyInterval, PVar, NVar, Fixed, M) ->
    Ty = ty_rec:interval(dnf_var_int:int(TyInterval)),
    % ntlv rule
    ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:interval(dnf_var_int:var(Var)) end, M).

substitute(_, Ty, _, _) -> Ty.
% there is nothing to substitute in a ty_interval
map_pi(_) -> #{}.
all_variables(_, _) -> [].

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
    Ia = ty_interval:interval(5, '*'),
    Ib = ty_interval:cointerval(2, 10),
    Ix = ty_interval:intersect(Ia, Ib),
    false = ty_interval:is_empty(Ix),
    Ic = ty_interval:interval(1, 1),
    true = ty_interval:is_empty(ty_interval:intersect(Ix, Ic)),

    ok.

-endif.
