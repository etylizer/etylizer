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
  all_variables/2
]).

-export_type([type/0]).

-opaque type() :: 0 | 1.
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type ast_ty() :: ast:ty().

reorder(X) -> X.
-spec compare(T, T) -> eq | lt | gt when T :: type().
compare(X, X) -> eq; compare(1, 0) -> gt; compare(0, 1) -> lt.
-spec empty() -> type().
empty() -> 0.
-spec any() -> type().
any() -> 1.
-spec union(T, T) -> T when T :: type().
union(X, Y) -> erlang:max(X, Y).
-spec intersect(T, T) -> T when T :: type().
intersect(X, Y) -> erlang:min(X, Y).
-spec difference(T, T) -> T when T :: type().
difference(_, 1) -> 0; difference(X, _) -> X.
-spec negate(T) -> T when T :: type().
negate(1) -> 0; negate(0) -> 1.
-spec is_any(type()) -> boolean().
is_any(1) -> true; is_any(_) -> false.
-spec is_empty(type(), T) -> {boolean(), T}.
is_empty(0, S) -> {true, S}; is_empty(_, S) -> {false, S}.

-spec normalize(type(), _, T) -> {set_of_constraint_sets(), T}.
normalize(Dnf, _, ST) ->
  case is_empty(Dnf, #{}) of
    {true, _} -> {[[]], ST};
    {false, _} -> {[], ST}
  end.

-spec unparse(type(), T) -> {ast_ty(), T}.
unparse(0, ST) -> {{predef, none}, ST};
unparse(1, ST) -> {{predef, any}, ST}.
 
-spec all_variables(type(), _) -> sets:set().
all_variables(_, _) -> sets:new().
