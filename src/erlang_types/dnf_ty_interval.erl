-module(dnf_ty_interval).

%% representation
%% left? range* right?

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

is_empty([], ST) -> {true, ST};
is_empty(_, ST) -> {false, ST}.

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

difference(I1, I2) ->
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

normalize(Dnf, _Fixed, ST) ->
  % Fig. 3 Line 3
  case is_empty(Dnf, #{}) of
    {true, _} -> {[[]], ST};
    {false, _} -> {[], ST}
  end.



unparse([], _) -> {predef, none};
unparse([any_int], _) -> {predef, any};
unparse([Int | Others], C) -> {union, [unparse_single(Int), unparse(Others, C)]}.

unparse_single({range, A, B}) -> {range, A, B};
unparse_single({left, -1}) -> {predef_alias, neg_integer};
unparse_single({right, 1}) -> {predef_alias, pos_integer};

unparse_single({left, L}) when L < -1 ->
  {intersection, [
                  {predef_alias, neg_integer}, 
                  {negation, unparse_single({range, (L + 1), -1})}
                 ]};
unparse_single({left, L}) when L > -1 ->
  {union, [{predef_alias, neg_integer}, unparse_single({range, -1, L})]};

unparse_single({right, R}) when R > 1 ->
  {intersection, [{predef_alias, pos_integer}, unparse_single({range, 1, (R - 1)})]};
unparse_single({right, R}) when R < 1 ->
  {union, [{predef_alias, pos_integer}, unparse_single({range, R, 1})]}.
