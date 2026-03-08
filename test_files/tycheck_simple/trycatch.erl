-module(trycatch).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% TRY-CATCH %%%%%%%%%%%%%%%%%%%%%%%

% minimal
-spec try_01() -> ok.
try_01() -> try ok catch _ -> ok end.

% error class
-spec try_02() -> caught.
try_02() -> try error(boom) catch error:boom -> caught end.

% union of body and catch
-spec try_03() -> ok | caught.
try_03() -> try ok catch _ -> caught end.

% even though in this case (pure function) we know that nothing will be catched
% we can't know it in general so we assume caught can be returned as well
-spec try_04_fail() -> ok.
try_04_fail() -> try ok catch _ -> caught end.

% wildcard pattern
-spec try_05() -> caught.
try_05() -> try error(anything) catch _:_ -> caught end.

% exit class
-spec try_06() -> caught.
try_06() -> try exit(normal) catch exit:normal -> caught end.

% stacktrace binding
-spec try_07() -> {caught, any()}.
try_07() -> try error(boom) catch error:boom:Stack -> {caught, Stack} end.

% of section
-spec try_08(integer()) -> ok | ok2.
try_08(X) -> try X of 1 -> ok; _ -> ok2 catch _:_ -> ok end.

% of section and catch
-spec try_09(integer()) -> ok | error.
try_09(X) -> try X of 1 -> ok; _ -> throw(error) catch throw:error -> error end.

% after section
-spec try_10() -> ok.
try_10() -> try ok after noop end.

% Try-catch with catch and after
-spec try_11() -> ok | caught.
try_11() -> try throw(error) catch throw:error -> caught after ok end.

% of, catch, and after
-spec try_12(integer()) -> ok | caught.
try_12(X) ->
    try X of
        1 -> throw(error);
        _ -> ok
    catch throw:error -> caught
    after ok end.

% union of catch return types
-spec try_13() -> ok | error.
try_13() -> try throw(x) catch throw:x -> error; throw:y -> ok end.

-spec try_14_fail() -> ok.
try_14_fail() -> try error catch _:_ -> ok end.

% guard in catch clause must be boolean, X + 1 is integer
-spec try_15_fail() -> any().
try_15_fail() ->
    try throw(42)
    catch throw:X when X + 1 -> X
    end.

% catch clause with guard
-spec try_16() -> integer() | other.
try_16() ->
    try throw(42)
    catch
        throw:X when is_integer(X) -> X;
        throw:_ -> other
    end.

% implicit throw class (pattern without class)
-spec try_17() -> ok.
try_17() -> try throw(error) catch error -> ok end.

% variable from try body visible in of section
-spec try_20() -> ok.
try_20() -> try X = ok, X of _ -> X catch _:_ -> ok end.

% nested
-spec try_21() -> ok | foo.
try_21() ->
    try try throw(inner) catch throw:inner -> foo end catch throw:outer -> ok end.

% catch with variable binding in exception type
-spec try_22() -> throw | error | exit.
try_22() ->
    try
        throw(x)
    catch
        Class:_ when Class =:= throw -> throw;
        Class:_ when Class =:= error -> error;
        Class:_ when Class =:= exit -> exit
    end.

% wildcard for all exception parts
-spec try_23() -> caught.
try_23() -> try error(boom) catch _:_:_ -> caught end.

-spec try_24(boolean()) -> ok | error.
try_24(X) ->
    try
        case X of
            true -> throw(ok);
            false -> error
        end
    catch
        throw:ok -> ok;
        throw:error -> error
    end.
