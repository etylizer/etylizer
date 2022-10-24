-module(test_utils_test).

-compile(export_all).
-compile(nowarn_export_all).

%-ety({test, bad, "Blub"}).
foo(X) -> X.

bar(X) -> X + 1.

%-ety({test, good}).

spam(X) -> X.
