-module(union_distrib_fail).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo({atom(), string()} | {boolean(), string()}) -> {integer() | boolean(), string()}.
foo(X) -> X.
