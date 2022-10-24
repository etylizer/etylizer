-module(funcall).

-compile(export_all).
-compile(nowarn_export_all).

bar(X, Y) -> X + Y.
foo(X) -> bar(X, 1).
spam() -> lists:map(fun (X) -> foo(X) end, [1,2,3]).
higher_order(F, X) -> F(X).
test() -> higher_order(fun foo/1, 1).
test2() -> higher_order(fun mod:foo/1, 1).
my_len(L) -> length(L).
