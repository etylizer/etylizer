-module(dnf_ty_bitstring).

% currently only supported: bitstring yes/no

-export([
  reorder/1,
  compare/2,
  empty/0,
  any/0,
  union/2,
  intersect/2,
  difference/2,
  negate/1,
  is_any/1,
  is_empty/2,
  normalize/3,
  unparse/2,
  all_variables/2,
  has_negative_only_line/1
]).

-include("erlang_types.hrl").

-export_type([type/0]).

-opaque type() :: 0 | 1.

-spec reorder(X) -> X when X :: type().
reorder(X) -> X.
-spec compare(T, T) -> eq | lt | gt when T :: type().
compare(X, Y) when X < Y -> lt;
compare(X, Y) when X > Y -> gt;
compare(_, _) -> eq.
-spec empty() -> type().
empty() -> 0.
-spec any() -> type().
any() -> 1.
-spec union(T, T) -> T when T :: type().
union(X, Y) -> erlang:max(X, Y).
-spec intersect(T, T) -> T when T :: type().
intersect(X, Y) -> erlang:min(X, Y).
-spec difference(T, T) -> T when T :: type().
difference(_, 1) -> 0; difference(X, _Y) -> X.
-spec negate(T) -> T when T :: type().
negate(1) -> 0; negate(0) -> 1.
-spec is_any(type()) -> boolean().
is_any(1) -> true; is_any(_) -> false.
-spec is_empty(type(), T) -> {boolean(), T}.
is_empty(0, S) -> {true, S}; is_empty(_, S) -> {false, S}.

-spec normalize(type(), _, T) -> {constraint_set:set_of_constraint_sets(), T}.
normalize(Dnf, _, ST) ->
  case is_empty(Dnf, #{}) of
    {true, _} -> {constraint_set:sat(), ST};
    {false, _} -> {constraint_set:unsat(), ST}
  end.

-spec unparse(type(), T) -> {ast_ty(), T}.
unparse(0, ST) -> {{predef, none}, ST};
unparse(1, ST) -> {{predef, any}, ST}.
 
-spec all_variables(type(), all_variables_cache()) -> sets:set(variable()).
all_variables(_, _) -> sets:new().

-spec has_negative_only_line(type()) -> boolean().
has_negative_only_line(_) -> false.

