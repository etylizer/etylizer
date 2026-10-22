-module(asserted).
-export([first/1, int/1, inc/1, twice/1, call/2, field/1, field_name/1]).

-define(INC(X), X + 1).
-define(TWICE(X), {X, X}).

% Each function needs an assertion to type check.

-spec first(list()) -> term().
first(L) ->
    [X | _] = L,
    X.

-spec int(term()) -> integer().
int(X) -> X.

-spec inc(term()) -> integer().
inc(X) -> ?INC(X).

-spec twice(term()) -> {integer(), integer()}.
twice(X) -> ?TWICE(X).

-spec call(term(), integer()) -> integer().
call(F, X) -> F(X).

-record(r, {f :: term()}).

-spec field(#r{}) -> integer().
field(R) -> R#r.f.

% the field name is no expression
-spec field_name(#r{}) -> term().
field_name(R) -> R#r.f.
