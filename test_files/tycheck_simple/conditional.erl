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
