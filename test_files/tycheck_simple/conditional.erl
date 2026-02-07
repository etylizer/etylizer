-module(conditional).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail

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

% exhaustiveness
-spec if_06(integer()) -> ok.
if_06(X) ->
    if is_integer(X) -> ok end.

% scoping of variables outside of the if expression if they are safe
-spec if_15() -> ok.
if_15() ->
    if true -> S = ok end,
    S.

-spec if_16_fail() -> ok.
if_16_fail() ->
    if true -> S = foo end,
    S.

% safe variable scope, S has type ok
-spec if_17(integer() | atom()) -> ok.
if_17(X) ->
    if is_integer(X) -> S = ok; 
       is_atom(X) -> S = ok end,
    S.

% S has type foo | bar
-spec if_18(integer() | atom()) -> foo | bar.
if_18(X) ->
    if is_integer(X) -> S = foo;
       is_atom(X) -> S = bar
    end,
    S.

% S has type foo | fail
-spec if_20_fail(integer() | atom()) -> foo | bar.
if_20_fail(X) ->
    if is_integer(X) -> S = foo;
       is_atom(X) -> S = fail
    end,
    S.

% S has type foo | bar
-spec if_21_fail(integer() | atom()) -> foo.
if_21_fail(X) ->
    if is_integer(X) -> S = foo;
       is_atom(X) -> S = bar
    end,
    S.

% begin scoping
-spec if_25() -> ok.
if_25() ->
    begin if true -> S = ok end end,
    S.
