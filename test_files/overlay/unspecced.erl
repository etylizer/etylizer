-module(unspecced).
-export([inc/1, use/0]).

inc(X) -> X + 1.

% a type error once inc/1 has the spec of the overlay
-spec use() -> integer().
use() -> inc(a).
