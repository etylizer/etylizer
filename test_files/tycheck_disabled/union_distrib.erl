-module(union_distrib).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo({integer(), string()} | {boolean(), string()}) -> {integer() | boolean(), string()}.
foo(X) -> X.
