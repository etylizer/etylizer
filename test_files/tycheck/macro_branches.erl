-module(macro_branches).

-compile(export_all).
-compile(nowarn_export_all).

% Both clauses have the location of the macro call. Each of them is unmatched for
% one alternative of the spec, but none for both.
-define(SEL(X), case X of a -> 1; b -> 2 end).

-spec foo(a) -> 1; (b) -> 2.
foo(X) -> ?SEL(X).
