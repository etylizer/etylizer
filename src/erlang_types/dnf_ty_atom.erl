-module(dnf_ty_atom).

-export([
  compare/2,
  empty/0,
  any/0,
  finite/1,
  cofinite/1,
  negate/1,
  intersect/2,
  union/2,
  difference/2,
  is_empty/2,
  is_any/1,
  normalize/3,
  unparse/2,
  all_variables/2
]).

-export_type([type/0]).

-opaque type() :: {gb_sets:set(), finite | cofinite}.
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type ast_ty() :: ast:ty().

-spec compare(T, T) -> eq | lt | gt when T :: type().
compare(R1, R2) -> case R1 < R2 of true -> lt; _ -> case R1 > R2 of true -> gt; _ -> eq end end.

-spec empty() -> type().
empty() -> {gb_sets:new(), finite}.

-spec any() -> type().
any() -> {gb_sets:new(), cofinite}.

-spec finite([atom()]) -> type().
finite([]) -> any();
finite([X | Xs]) -> intersect({gb_sets:from_list([X]), finite}, finite(Xs)).

-spec cofinite([atom()]) -> type().
cofinite(ListOfBasic) -> {gb_sets:from_list(ListOfBasic), cofinite}.

-spec negate(T) -> T when T :: type().
negate({S, finite}) -> {S, cofinite};
negate({S, cofinite}) -> {S, finite}.

% HACK pattern match on gb_sets:new() representation
-spec intersect(T, T) -> T when T :: type().
intersect(_, Z = {{0, nil}, finite}) -> Z;
intersect(Z = {{0, nil}, finite}, _) -> Z;
intersect({{0, nil}, cofinite}, S) -> S;
intersect(S, {{0, nil}, cofinite}) -> S;
intersect(S = {_, cofinite}, T = {_, finite}) -> intersect(T, S);
intersect({S, finite}, {T, finite}) ->
  {gb_sets:intersection(S, T), finite};
intersect({S, finite}, {T, cofinite}) ->
  {gb_sets:difference(S, T), finite};
intersect({S, cofinite}, {T, cofinite}) ->
  {gb_sets:union(S,T), cofinite}.

-spec union(T, T) -> T when T :: type().
union(S,T) -> negate(intersect(negate(S), negate(T))).

-spec difference(T, T) -> T when T :: type().
difference(S,T) -> intersect(S, negate(T)).

-spec is_empty(type(), T) -> {boolean(), T}.
is_empty(Rep, ST) ->
  case Rep of
    {{0, nil}, finite} -> {true, ST};
    _ -> {false, ST}
  end.

-spec is_any(type()) -> boolean().
is_any(Rep) ->
  case Rep of
    {{0, nil}, cofinite} -> true;
    _ -> false
  end.

-spec normalize(type(), _, T) -> {set_of_constraint_sets(), T}.
normalize(Dnf, _Fixed, ST) ->
  % Fig. 3 Line 3
  case is_empty(Dnf, #{}) of
    {true, _} -> {[[]], ST};
    {false, _} -> {[], ST}
  end.

-spec unparse(type(), T) -> {ast_ty(), T}.
unparse({Atoms, finite}, ST) ->
  {ast_lib:mk_union(lists:map(fun(A) -> {singleton, A} end, gb_sets:to_list(Atoms))), ST};
unparse({Atoms, cofinite}, ST) ->
  {ast_lib:mk_negation(ast_lib:mk_union(lists:map(fun(A) -> {singleton, A} end, gb_sets:to_list(Atoms)))), ST}.

-spec all_variables(type(), _) -> sets:set().
all_variables(_, _) -> sets:new().
