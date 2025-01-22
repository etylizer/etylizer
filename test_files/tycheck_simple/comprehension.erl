-module(comprehension).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

% Test for a scoping bug
% Currently deactivated because we have no support for list comprehension #151
% -spec foo(list(T)) -> list({T, T}).
% foo(Alts) -> [{S, A} || A <- Alts, S=A].
