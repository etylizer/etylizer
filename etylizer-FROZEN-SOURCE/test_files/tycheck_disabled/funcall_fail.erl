-module(funcall_fail).

-export([bar/1]).

% With set-theoretic types, this test could succeed because
% "boolean() -> boolean()" (the type of F) is a subtype of
% "none() -> integer()", so the call F(throw("error")) typechecks
% and returns an integer.
%
% However, we prefer the function call to fail for design
% and performance reasons.
-spec bar(fun((boolean()) -> boolean())) -> integer().
bar(F) -> F(throw("error")).
