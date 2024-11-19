-module(alias).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail

-spec id(fun((A) -> B), A) -> B.
id(Fun, Xa) -> Fun(Xa).

-spec id2(fun((A) -> B), A) -> Xb when Xb :: B.
id2(Fun, Xa) -> Fun(Xa).
