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

% See #141
-spec pin([number()]) -> boolean() | falsee.
pin(L) ->
    X = 1,
    case L of
        X -> true;
        [X | _] -> falsee;
        _ -> false
    end.

-spec case_14(_, _) -> ok | nok.
case_14(X, X) -> ok;
case_14(_, _) -> nok.

% scoping of variables outside of the case expression if they are safe
-spec case_15() -> ok.
case_15() ->
    case foo of _ -> S = ok end,
    S.

-spec case_16_fail() -> ok.
case_16_fail() ->
    case ok of _ -> S = foo end,
    S.

% safe variable scope
-spec case_17(foo | bar) -> ok.
case_17(X) ->
    case X of foo -> S = ok; bar -> S = ok end,
    S.

% S has type foo | bar
-spec case_18(foo | bar) -> foo | bar.
case_18(X) ->
    case X of 
        foo -> S = foo; 
        bar -> S = bar
    end,
    S.

% S has type foo
-spec case_19(foo | bar) -> foo | bar.
case_19(X) ->
    case X of 
        foo -> S = foo; 
        bar -> S = foo
    end,
    S.

% S has type foo | fail
-spec case_20_fail(foo | bar) -> foo | bar.
case_20_fail(X) ->
    case X of 
        foo -> S = foo; 
        bar -> S = fail
    end,
    S.

% S has type foo | bar
% the case expression is exhaustive
-spec case_21_fail(foo | bar) -> foo.
case_21_fail(X) ->
    case X of
        S when S == foo -> S;
        S when S == bar -> foo
    end,
    S.

% disabled until == refinement
% S has type foo | bar
% the case expression is exhaustive
-spec case_22(foo | bar) -> foo | bar.
case_22(X) ->
    case X of
        S when S == foo -> S;
        S when S == bar -> foo
    end,
    S.

% disabled until == refinement
-spec case_23(foo | bar) -> ok.
case_23(X) ->
    case X of
        S when S == foo -> ok;
        S when S == bar -> ok
    end.

-spec case_24(integer()) -> integer().
case_24(X) ->
    case X of
        Y when is_integer(Y) -> Y
    end.

% begin scoping
-spec case_25() -> ok.
case_25() ->
    begin case foo of _ -> S = ok end end,
    S.

% exhaustiveness with variables from outer scope
-spec case_26(integer()) -> ok.
case_26(X) ->
    case {} of _ when is_integer(X) -> ok end.

% Tests that guard {S, complex} == {foo, complex} correctly refines S to foo
-spec case_27(foo | bar) -> foo | bar.
case_27(X) ->
    case X of
        S when {S, complex} == {foo, complex} -> S;
        S -> S
    end,
    S.

-spec case_28_fail(foo | bar) -> bar.
case_28_fail(X) ->
    case X of
        S when {S, complex} == {foo, complex} -> S;
        S -> S
    end,
    S.

% symmetry
-spec case_29(foo | bar) -> foo | bar.
case_29(X) ->
    case X of
        S when {foo, complex} == {S, complex} -> S;
        S -> S
    end,
    S.

-spec case_30_fail(foo | bar) -> bar.
case_30_fail(X) ->
    case X of
        S when {foo, complex} == {S, complex} -> S;
        S -> S
    end,
    S.

% #295 variable bound in case scrutinee should be visible in clause bodies
-spec case_31() -> ok.
case_31() ->
    case U = ok of
        _ -> U
    end.

-spec case_32(boolean()) -> ok | error.
case_32(X) ->
    case X of
        true -> throw(ok);
        false -> error
    end.


-spec case_33_fail(fun((atom() | reference(), term()) -> [tuple()]), term()) -> term().
case_33_fail(F, Ref) ->
  [{Ref, Node}] =
  case F(myetstable, Ref) of
      __Z = [{Ref, _}] -> __Z; _ -> error(badarg)
  end,
  Node.

% Dispatch optimization: position 2 is always a simple variable (direct),
% position 1 has complex patterns including catch-alls with guards.
% The optimizer should dispatch only on position 1.
-spec case_34(term(), atom()) -> atom().
case_34({ok, _}, Tag) -> Tag;
case_34({error, _}, Tag) -> Tag;
case_34(Tuple, Tag) when is_tuple(Tuple) -> Tag;
case_34([_|_], Tag) -> list;
case_34(Map, _Tag) when is_map(Map) -> map;
case_34(_Term, _Tag) -> other.

% Dispatch optimization with intersection type spec.
% Catch-all in complex position should not cause false errors.
-spec case_35({ok, term()}, atom()) -> ok;
             (error, atom()) -> error.
case_35({ok, _}, _Tag) -> ok;
case_35(error, _Tag) -> error.

