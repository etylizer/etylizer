-module(special).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

-etylizer({functions_exhaustive, off, [error03/1, error04/1]}).
-etylizer({functions_redundant, off, [error01/1, error05/1]}).

%%%%%%%%%%%%%%%%%%%%%%%% erlang:error-only function clauses %%%%%%%%%%%%%%%%%%%%%%%

% This module tests the disable_redundancy_toplevel and
% disable_exhaustiveness_toplevel attributes for handling function clauses
% that exist only for runtime error reporting (e.g. badarg guards).

% error clause is redundant w.r.t. the spec, but acceptable with disable_redundancy_toplevel
-spec error01(integer()) -> ok.
error01(I) when is_integer(I) -> ok;
error01(_) -> error(custom_error_msg).

% without disable_redundancy_toplevel, the error clause is detected as redundant
-spec error02_fail(integer()) -> ok.
error02_fail(I) when is_integer(I) -> ok;
error02_fail(_) -> error(custom_error_msg).

% disabled top-level exhaustiveness with annotation
-spec error03(integer()) -> ok.
error03(1) -> ok.

% adding exhaustiveness to already exhaustive function should pass (exhaustive check off)
-spec error04(integer()) -> ok.
error04(_) -> ok.

% redundant error clause accepted with disable_redundancy_toplevel
-spec error05(1 | 2) -> ok.
error05(1) -> error(impl);
error05(2) -> ok;
error05(_) -> error(badarg).
