-module(features).
-export([a/1, b/1, c/1, d/1]).
-spec a(integer() | atom()) -> ok.
a(_) -> ok.
-spec b(X) -> X.
b(X) -> X.
-spec c(integer()) -> ok; (atom()) -> ok.
c(_) -> ok.
d(X) -> X.
