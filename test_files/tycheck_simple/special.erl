-module(special).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

-disable_exhaustiveness_toplevel([error01_e_fail/1, error06/1, error08_fail/1]).
-disable_exhaustiveness([error11/1]).

%%%%%%%%%%%%%%%%%%%%%%%% erlang:error-only function clauses %%%%%%%%%%%%%%%%%%%%%%%

% Heuristic for Error-Only Function Clauses
% This module tests a heuristic for handling function clauses that
% only contain `error/1` calls (or `error/2` calls). 
% The purpose is to enable fine-grained error messages when 
% a value/clause is outside of the type specification.
%
% * We enable this heuristic only for functions with more than one clause
% * Only removes the last clause if it's an error clause
% * The interaction with disable_exhaustiveness_toplevel is as follows: 
%   first the clauses are filtered, then the exhaustiveness clause is added at the end

% error-less clauses equal to spec
-spec error01(integer()) -> ok.
error01(I) when is_integer(I) -> ok;
error01(_) -> error(custom_error_msg).

% added exhaustiveness: should fail 
% we only remove one error clause
% the second one will be detected as redundant
-spec error01_e_fail(integer()) -> ok.
error01_e_fail(I) when is_integer(I) -> ok;
error01_e_fail(_) -> error(custom_error_msg).
%error01_e_fail(_) -> error(exhaustiveness).

% error-less clauses bigger than spec also should fail (redundant clause)
-spec error02_fail(integer()) -> ok.
error02_fail(I) when is_integer(I) -> ok;
error02_fail(F) when is_float(F) -> ok;
error02_fail(_) -> error(custom_error_msg).

% error-less clauses less than spec should still fail (exhaustiveness)
-spec error03_fail(integer()) -> ok.
error03_fail(1) -> ok;
error03_fail(_) -> error(custom_error_msg).

% mock implementations should be accepted
-spec error04(integer()) -> ok.
error04(_) -> error(single_clause).

% cases with an error clause should still be treated as before
-spec error05(atom()) -> bar.
error05(A) -> 
  case A of
    foo -> bar;
    _ -> error(todo)
  end.

% disabled top-level exhaustiveness with annotation
-spec error06(integer()) -> ok.
error06(1) -> ok.
% error06(_) -> error(exhaustiveness).

-spec error07(integer()) -> ok.
error07(_) -> ok.

% adding exhaustiveness to already exhaustive function should fail
-spec error08_fail(integer()) -> ok.
error08_fail(_) -> ok.
% error08_fail(_) -> error(exhaustiveness).

-spec error09(1 | 2) -> ok.
error09(1) -> error(impl);
error09(2) -> ok.

-spec error10(1 | 2) -> ok.
error10(1) -> error(impl);
error10(2) -> ok;
error10(_) -> error(badarg).

% disabled exhaustiveness completely
-spec error11(atom()) -> bar.
error11(A) -> 
  case A of
    foo -> bar
  end.
