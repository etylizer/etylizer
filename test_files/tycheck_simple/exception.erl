-module(exception).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

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
