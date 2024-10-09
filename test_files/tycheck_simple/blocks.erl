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
