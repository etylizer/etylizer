-module(blocks).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

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

% #22
-spec block_04() -> boolean().
block_04() ->
    begin
        A = 1,
        is_integer(A)
    end
        orelse
        is_float(A).

% #230
-spec block_05() -> any().
block_05() ->
    Now = {_Mega, _Sec, _Micro} = erlang:timestamp(),
    Now.
