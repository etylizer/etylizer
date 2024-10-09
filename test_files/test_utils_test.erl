-module(test_utils_test).

-compile(export_all).
-compile(nowarn_export_all).

%-etylizer({test, bad, "Blub"}).
foo(X) -> X.

bar(X) -> X + 1.

%-etylizer({test, good}).

spam(X) -> X.
