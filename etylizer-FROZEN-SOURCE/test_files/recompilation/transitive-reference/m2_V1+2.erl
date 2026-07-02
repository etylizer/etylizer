-module(m2).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(m3:t()) -> integer().
bar(X) -> X.
