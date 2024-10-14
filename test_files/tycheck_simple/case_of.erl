-module(case_of).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

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

% The type checker fails with "not all cases are covered" because it is too stupid
% when matching against bound variables in patterns (such as X).
-spec case_13_fail(1, 1) -> 2.
case_13_fail(X, A) ->
  case A of
    X -> 2
  end.

