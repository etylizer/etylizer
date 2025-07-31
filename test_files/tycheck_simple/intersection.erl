-module(intersection).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% INTERSECTION %%%%%%%%%%%%%%%%%%%%%%%%

-spec use_atom(atom()) -> atom().
use_atom(X) -> X.

-spec inter_01(integer()) -> integer(); (atom()) -> atom().
inter_01(X) ->
    case X of
        _ when is_integer(X) -> X + 1;
        _ -> use_atom(X)
    end.

% just swap the types of the intersection
-spec inter_02(atom()) -> atom(); (integer()) -> integer().
inter_02(X) ->
    case X of
        _ when is_integer(X) -> X + 1;
        _ -> use_atom(X)
    end.

-spec inter_03_fail(integer()) -> integer(); (atom()) -> atom().
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
        [_X | XS] -> XS + 1
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

-spec foo([T]) -> [T].
foo(L) ->
    case L of
        [] -> [];
        [_X|XS] -> XS
    end.

-spec foo2_case(a) -> 1; (b) -> 2.
foo2_case(X) ->
    case X of
        a -> 1;
        b -> 2
    end.

-spec foo3(a|b) -> 1|true.
foo3(a) -> 1;
foo3(b) -> true.

% See #56
-spec foo4
    (integer()) -> integer();
    (1) -> 2.
foo4(X) ->
    case X of
        1 -> 2;
        _ -> X
    end.
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

-spec scrutiny_with_redundant_branch(1) -> 100; (2) -> 200.
scrutiny_with_redundant_branch(X) ->
    case
        case X of
            1 -> 10;
            2 -> 20
        end
    of
        10 -> 100;
        20 -> 200
    end.

-spec scrutiny_with_redundant_branch_fail(1) -> 100; (2) -> 200.
scrutiny_with_redundant_branch_fail(X) ->
    case
        case X of
            1 -> 11;
            2 -> 20
        end
    of
        10 -> 100;
        20 -> 200
    end.

-spec scrutiny_with_redundant_branch_local_fun(1) -> 100; (2) -> 200.
scrutiny_with_redundant_branch_local_fun(Z) ->
    F = fun(X) ->
            case
                case X of
                    1 -> 10;
                    2 -> 20
                end
            of
                10 -> 100;
                20 -> 200
            end
        end,
    F(Z).

-spec scrutiny_with_redundant_branch_local_fun_fail(1) -> 100; (2) -> 200.
scrutiny_with_redundant_branch_local_fun_fail(Z) ->
    F = fun(X) ->
            case
                case X of
                    1 -> 10;
                    2 -> 21
                end
            of
                10 -> 100;
                20 -> 200
            end
        end,
    F(Z).

-spec branch_unmatched_in_all_intersections_fail(1) -> 10; (2) -> 20.
branch_unmatched_in_all_intersections_fail(X) ->
    case X of
        1 -> 10;
        2 -> 20;
        3 -> 30
    end.
