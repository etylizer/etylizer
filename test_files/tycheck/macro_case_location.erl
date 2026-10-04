-module(macro_case_location).

-compile(export_all).
-compile(nowarn_export_all).

% The case and its first clause have the location of the macro call. Each clause is
% unmatched for one alternative of the spec, but none for both.
-define(SEL(A, B), case X of a -> A; b -> B end).

-spec foo(a) -> 1; (b) -> 2.
foo(X) -> ?SEL((1), (2)).
