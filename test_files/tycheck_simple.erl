-module(tycheck_simple).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% ATOMS %%%%%%%%%%%%%%%%%%%%%%%s
-spec atom_01() -> foobar.
atom_01() -> foobar.

-spec atom_02() -> atom().
atom_02() -> foobar.

-spec atom_03_fail() -> integer().
atom_03_fail() -> foobar.

-spec atom_04_fail() -> foobar.
atom_04_fail() -> 1.

-spec atom_05_fail() -> atom().
atom_05_fail() -> 1.

-spec atom_06_fail() -> foobar.
atom_06_fail() -> spam.

% Chars
-spec char_01() -> $a.
char_01() -> $a.

-spec char_02() -> char().
char_02() -> $a.

-spec char_03() -> integer().
char_03() -> $a.

-spec char_04_fail() -> atom().
char_04_fail() -> $a.

-spec char_05_fail() -> $a.
char_05_fail() -> foobar.

-spec char_06_fail() -> $a.
char_06_fail() -> 1.

-spec char_07() -> $a.
char_07() -> 97. % ascii code for a

-spec char_08_fail() -> char().
char_08_fail() -> foobar.

-spec char_09_fail() -> $a.
char_09_fail() -> $b.

%%%%%%%%%%%%%%%%%%%%%%%% INTEGERS %%%%%%%%%%%%%%%%%%%%%%%

-spec integer_01() -> 42.
integer_01() -> 42.

-spec integer_02() -> integer().
integer_02() -> 42.

-spec integer_03_fail() -> atom().
integer_03_fail() -> 42.

-spec integer_04_fail() -> 42.
integer_04_fail() -> foobar.

-spec integer_05_fail() -> integer().
integer_05_fail() -> foobar.

-spec integer_06_fail() -> 42.
integer_06_fail() -> 43.

-spec integer_07() -> number().
integer_07() -> 42.

%%%%%%%%%%%%%%%%%%%%%%%% FLOATS %%%%%%%%%%%%%%%%%%%%%%%

-spec float_01() -> float().
float_01() -> 3.14.

-spec float_02() -> float().
float_02() -> 42.0.

-spec float_03() -> number().
float_03() -> 3.14.

-spec float_04_fail() -> float().
float_04_fail() -> "bass".

-spec float_05_fail() -> atom().
float_05_fail() -> 3.14.

%%%%%%%%%%%%%%%%%%%%%%%% STRINGS %%%%%%%%%%%%%%%%%%%%%%%

-spec string_01() -> string().
string_01() -> "bass".

-spec string_02() -> string().
string_02() -> "".

-spec string_03() -> [].
string_03() -> "".

-spec string_04() -> [char()].
string_04() -> "bass".

-spec string_05_fail() -> string().
string_05_fail() -> 1.

-spec string_06_fail() -> [atom()].
string_06_fail() -> "bass".

-spec string_07() -> [integer()].
string_07() -> "bass".

-spec string_08_fail() -> 1.
string_08_fail() -> "bass".

%%%%%%%%%%%%%%%%%%%%%%%% SIMPLE FUNCTIONS %%%%%%%%%%%%%%%%%%%%%%%

-spec fun_01(any()) -> any().
fun_01(X) -> X.

-spec fun_02_fail(integer()) -> atom().
fun_02_fail(X) -> X.

-spec fun_03(string(), integer()) -> integer().
fun_03(_X, Y) -> Y.

-spec fun_04_fail(string(), integer()) -> integer().
fun_04_fail(X, _Y) -> X.

-spec fun_05(integer()) -> any().
fun_05(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% OPERATORS %%%%%%%%%%%%%%%%%%%%%%%

-spec op_01() -> integer().
op_01() -> 1 + 2.

-spec op_02() -> boolean().
op_02() -> 1 =:= 2.

-spec op_03() -> integer().
op_03() -> -3.

% fails in gradualizer with
% "The integer on line 147 at column 13 is expected to have type integer but it has type 1"
-spec op_04() -> list(integer()).
op_04() -> [1,2] ++ [3,4].

-spec op_05() -> boolean().
op_05() -> 1 =:= "foo".

-spec op_06_fail(integer()) -> boolean().
op_06_fail(X) -> X + "foo".

-spec op_07_fail() -> list(integer()).
op_07_fail() -> [1,2] ++ ["foo", "bar"].

-spec op_08() -> list().
op_08() -> [1,2] ++ ["foo", "bar"].

-spec op_09() -> list(integer()).
op_09() -> [] ++ [].

%%%%%%%%%%%%%%%%%%%%%%%% CASE %%%%%%%%%%%%%%%%%%%%%%%

-spec case_01(atom()) -> foobar.
case_01(X) ->
    case X of
        spam -> foobar;
        _ -> foobar
    end.

-spec case_02_fail(atom()) -> foobar.
case_02_fail(X) ->
    case X of
        spam -> foobar;
        Y -> Y
    end.

-spec case_03_fail(atom()) -> foobar.
case_03_fail(X) ->
    case X of
        spam -> egg;
        _ -> foobar
    end.

-spec case_04(atom()) -> foobar.
case_04(X) ->
    case X of
        foobar -> X; % fails in gradualizer
        _ -> foobar
    end.

-spec case_05_fail(atom()) -> foobar.
case_05_fail(X) ->
    case X of
        spam -> X;
        _ -> foobar
    end.

-spec case_06(any()) -> integer().
case_06(X) ->
    case X of
        Y when is_integer(Y) -> Y;
        _ -> 42
    end.

-spec case_07(any()) -> integer().
case_07(X) ->
    case X of
        _ when is_integer(X) -> X;
        _ -> 42
    end.

-spec case_08_fail(any(), any()) -> integer().
case_08_fail(X, Z) ->
    case Z of
        _ when is_integer(X) -> Z;
        _ -> 42
    end.

-spec case_09(any()) -> float().
case_09(X) ->
    case X of
        Y when is_float(Y) -> Y;
        _ -> 42.0
    end.

-spec case_10_fail(any()) -> integer().
case_10_fail(X) ->
    case X of
        % should fail because Y does not have type integer
        % in the guard but abs requires a number
        Y when abs(Y) > 2 andalso is_integer(Y) -> Y;
        _ -> 42
    end.

-spec case_11_fail(integer()) -> integer().
case_11_fail(X) ->
    case X of
        none -> 0 % branch cannot match
    end.

-spec case_12_fail(integer()) -> integer().
case_12_fail(X) ->
    case X of
        1 -> 0 % branch is not exhaustive
    end.

%%%%%%%%%%%%%%%%%%%%%%%% BLOCKS %%%%%%%%%%%%%%%%%%%%%%%

-spec block_01() -> integer().
block_01() ->
    X = 1 + 3,
    case X of
        4 -> 5;
        _ -> 42
    end.

-spec block_02_fail() -> integer().
block_02_fail() ->
    X = 1 + 3,
    case X of
        4 -> 5;
        _ -> foo
    end.

-spec block_03() -> 4.
block_03() ->
    _ = 1 + 3,
    _ = 4.

%%%%%%%%%%%%%%%%%%%%%%%% CATCH %%%%%%%%%%%%%%%%%%%%%%%

-spec catch_01() -> any().
catch_01() -> catch (2/10).

-spec catch_02() -> integer().
catch_02() ->
    X = catch (2/10),
    case X of
        Y when is_float(Y) -> floor(Y);
        _ -> 42
    end.

-spec catch_03_fail() -> float().
catch_03_fail() -> catch (1/10) + 1.

%%%%%%%%%%%%%%%%%%%%%%%% CONS, NIL %%%%%%%%%%%%%%%%%%%%%%%

-spec cons_01() -> list(integer()).
cons_01() -> [1 | [2 | []]].

-spec cons_02() -> list(any()).
cons_02() -> [1 | ["foo" | []]].

-spec cons_03() -> list(string() | integer()).
cons_03() -> [1 | ["foo" | []]].

-spec cons_04_fail() -> list(integer()).
cons_04_fail() -> [1 | [2 | 3]].

-spec cons_05() -> list().
cons_05() -> [1 | [2 | []]].

-spec cons_06_fail() -> [].
cons_06_fail() -> [1 | [2 | []]].

-spec nil_01() -> list(none()).
nil_01() -> [].

-spec nil_02() -> nil().
nil_02() -> [].

-spec nil_03() -> list().
nil_03() -> [].

-spec nil_04() -> list(any()).
nil_04() -> [].

-spec nil_05_fail() -> integer().
nil_05_fail() -> [].

-spec list_pattern_01(list(integer())) -> integer().
list_pattern_01(L) ->
    case L of
        [] -> 1;
        [X | _] -> X
    end.

-spec list_pattern_02(list(integer())) -> integer().
list_pattern_02(L) ->
    case L of
        [] -> 1;
        [_X, Y | _] -> Y;
        [X | _] -> X
    end.

-spec list_pattern_03_fail(list(integer())) -> integer().
list_pattern_03_fail(L) ->
    case L of
        % not exhaustive
        [X | _] -> X
    end.

-spec list_pattern_03(nonempty_list(integer())) -> integer().
list_pattern_03(L) ->
    case L of
        [X | _] -> X
    end.

-spec list_pattern_04_fail(list(integer())) -> integer().
list_pattern_04_fail(L) ->
    case L of
        [] -> 1;
        % not exhaustive
        [_X, Y | _] -> Y
    end.

-spec list_pattern_04b_fail(list(integer())) -> integer().
list_pattern_04b_fail(L) ->
    case L of
        [] -> 1;
        % not exhaustive
        [_X, []] -> 2
    end.

-spec list_pattern_05_fail(list(integer())) -> integer().
list_pattern_05_fail(L) ->
    case L of
        [] -> 1;
        [1 | _] -> 2 % not exhaustive
    end.

-spec list_pattern_06_fail(list(integer())) -> integer().
list_pattern_06_fail(L) ->
    case L of
        [] -> 1;
        [1 | _] -> 2;
        [_X] -> 3 % not exhaustive
    end.

-spec list_pattern_07(list(integer())) -> integer().
list_pattern_07(L) ->
    case L of
        [] -> 1;
        [1 | _] -> 2;
        [_X | _] -> 3
    end.

-spec list_pattern_08(list(integer())) -> integer().
list_pattern_08(L) ->
    case L of
        [] -> 1;
        [1 | _] -> 2;
        [1, 2 | _] -> 3; % redundant
        _ -> 4
    end.

%%%%%%%%%%%%%%%%%%%%%%%% FUN REF AND CALL %%%%%%%%%%%%%%%%%%%%%%%

-spec some_fun(string(), integer()) -> string().
some_fun(S, _) -> S.

-spec fun_ref_01() -> string().
fun_ref_01() -> some_fun("foo", 42).

-spec fun_ref_02_fail() -> integer().
fun_ref_02_fail() -> some_fun("foo", 42).

-spec fun_ref_03_fail() -> string().
fun_ref_03_fail() -> some_fun("foo", "42").

%%%%%%%%%%%%%%%%%%%%%%%% FUN %%%%%%%%%%%%%%%%%%%%%%%

-spec fun_local_01() -> integer().
fun_local_01() ->
    F = fun(X, Y) -> X + Y end,
    F(1, 2).

-spec fun_local_02() -> integer().
fun_local_02() ->
    F = fun Add(X) ->
        case X of
            0 -> 0;
            Y -> Y + Add(X - 1)
        end
        end,
    F(3).

-spec fun_local_03() -> integer().
fun_local_03() ->
    F = fun
            Add(0) -> 0;
            Add(X) -> X + Add(X + 1)
        end,
    F(3).

-spec fun_local_04() -> integer().
fun_local_04() ->
    F = fun
            Add(X) when X =:= 0 -> 0;
            Add(X) -> X + Add(X + 1)
        end,
    F(3).

-spec fun_local_05_fail(integer()) -> integer().
fun_local_05_fail(X) ->
    F = fun(Y) -> X + Y end,
    F("foo").

-spec fun_local_06() -> foobar.
fun_local_06() ->
  F = fun(X) ->
        case X of
            spam -> foobar;
            _ -> foobar
        end
      end,
  F(spam).

-spec fun_local_07(1) -> a; (2) -> b.
fun_local_07(X) ->
    F = fun(Y) ->
            case Y of
                1 -> a;
                2 -> b
            end
        end,
    F(X).

-spec fun_local_07_fail(1) -> a; (2) -> b.
fun_local_07_fail(X) ->
    F = fun(Y) ->
            case Y of
                1 -> c; % result c has wrong type (must be a)
                2 -> b
            end
        end,
    F(X).

%%%%%%%%%%%%%%%%%%%%%%%% IF %%%%%%%%%%%%%%%%%%%%%%%

-spec if_01(integer()) -> integer().
if_01(X) ->
    if X =:= 0 -> 42;
        true -> 0
    end.

-spec if_02(integer()) -> integer() | string().
if_02(X) ->
    if X =:= 0 -> 42;
        true -> "foo"
    end.

-spec if_03_fail(integer()) -> integer().
if_03_fail(X) ->
    if X =:= 0 -> 42;
        true -> "foo"
    end.

-spec if_04_fail(atom()) -> integer().
if_04_fail(X) ->
    if (X + 1) =:= 0 -> 0;
        true -> 1
    end.

-spec if_05(atom()) -> integer().
if_05(X) ->
    if X =:= 0 -> 0;
        true -> 1
    end.

%%%%%%%%%%%%%%%%%%%%%%%% TUPLES %%%%%%%%%%%%%%%%%%%%%%%

-spec tuple_01() -> {integer(), string()}.
tuple_01() -> {42, "foo"}.

-spec tuple_02_fail() -> {integer(), string()}.
tuple_02_fail() -> {"foo", 42}.

-spec tuple_03() -> {atom(), integer(), {boolean(), string()}}.
tuple_03() -> {foo, 42, {true, "foo"}}.

-spec tuple_04({atom(), integer()}) -> integer().
tuple_04(X) ->
    case X of
        {_, I} -> I
    end.

-spec tuple_05_fail({atom(), integer()}) -> integer().
tuple_05_fail(X) ->
    case X of
        {A, _} -> A
    end.

%%%%%%%%%%%%%%%%%%%%%%%% INTERSECTION %%%%%%%%%%%%%%%%%%%%%%%%

-spec use_atom(atom()) -> atom().
use_atom(X) -> X.

-spec inter_01(integer()) -> integer()
; (atom()) -> atom().
inter_01(X) ->
    case X of
        _ when is_integer(X) -> X + 1;
        _ -> use_atom(X)
    end.

% just swap the types of the intersection
-spec inter_02(atom()) -> atom()
; (integer()) -> integer().
inter_02(X) ->
    case X of
        _ when is_integer(X) -> X + 1;
        _ -> use_atom(X)
    end.

-spec inter_03_fail(integer()) -> integer()
; (atom()) -> atom().
inter_03_fail(X) ->
    case X of
        _ when is_integer(X) -> X + 1;
        _ -> X + 2
    end.

-spec inter_04_ok([T]) -> [T].
inter_04_ok(L) ->
    case L of
        [] -> [];
        [_X | XS] -> XS
    end.

-spec inter_04_fail([T]) -> [T] ; ([T]) -> [T].
inter_04_fail(L) ->
    case L of
        [] -> [];
        [_X | XS] -> XS + 1 % ERROR ignored if branch ignored when type-checking
    end.

-spec foo([T]) -> [T].
foo(L) ->
    case L of
        [] -> [];
        [_X|XS] -> XS
    end.

% See #36
-spec impossible_branch_f1(a) -> 1; (b) -> 2.
impossible_branch_f1(a) -> 1;
impossible_branch_f1(b) -> 2.

% See #36
-spec impossible_branch_f1_case(a) -> 1; (b) -> 2.
impossible_branch_f1_case(X) ->
    case X of
        a -> 1;
        b -> 2
    end.

% See #36
-spec impossible_branch_f2({a, integer()}) -> 1; ({b, integer()}) -> 2.
impossible_branch_f2(X) ->
    case X of
        {a, _} -> 1;
        {b, _} -> 2
    end.

% See #36
-spec impossible_branch_f3(a) -> 1; (b) -> 2.
impossible_branch_f3(X) ->
    case {X, 5}  of
        {a, _} -> 1;
        {b, _} -> 2
    end.

% See #36
-spec impossible_branch_f6(integer()) -> 2.
impossible_branch_f6(X) ->
    case X of
      2 -> X;
      _ -> 2
    end.

-spec foo3(a|b) -> 1|true.
foo3(a) -> 1;
foo3(b) -> true.

% See #56 and #36. In #36, the example is called f5
-spec foo4
    (integer()) -> integer();
    (1) -> 2.
foo4(X) ->
    case X of
        1 -> 2;
        _ -> X
    end.

% See #56
-spec foo4_b
    (integer()) -> integer();
    (1) -> 2.
foo4_b(X) ->
    case X of
        1 -> 2;
        3 -> 3;
        _ -> X
    end.

-spec inter_with_guard_constraints_fail(any()) -> integer(); (any()) -> integer().
inter_with_guard_constraints_fail(X) ->
    case X of
        % should fail because Y does not have type integer
        % in the guard but abs requires a number
        Y when abs(Y) > 2 andalso is_integer(Y) -> Y;
        _ -> 42
    end.

%%%%%%%%%%%%%%%%%%%%%%%% MISC %%%%%%%%%%%%%%%%%%%%%%%%

% same as fun_local_02 but transformed
% such that there are no n-tuples and n-functions anymore
-spec fun_local_02_plus() -> integer().
fun_local_02_plus() ->
    F = fun Add(X) ->
        case X of
            0 -> 0;
            Y -> my_plus({Y, Add(my_plus({X, -1}))})
        end
        end,
    F(3).

-spec my_plus({integer(), integer()}) -> integer(); ({float(), integer()}) -> float(); ({integer(), float()}) -> float(); ({float(), float()}) -> float().
my_plus({A, B}) -> A + B.

% The first branch of the case is not redundant
-spec poly(T) -> T.
poly(X) ->
    case X of
        1 -> X;
        _ -> X
    end.

-spec poly_inter(T) -> T; (T) -> T.
poly_inter(X) ->
    case X of
        1 -> X;
        _ -> X
    end.
