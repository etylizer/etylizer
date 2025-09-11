-module(ty_unique).

% helper constructors
-export([
  unique/1,

  is_empty/2,
  normalize/3,
  all_variables/2,

  equal/2,
  compare/2,
  assert_valid/1,
  unparse/2,

  any/0,
  empty/0,
  union/2,
  intersect/2,
  difference/2,
  negate/1,


  functions/1,
  tuples/1,
  list/1,
  predefined/1,
  bitstring/1,
  map/1,
  atom/1,
  interval/1,
  tuple_to_map/1
]).

-type monomorphic_variables() :: etally:monomorphic_variables().
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type variable() :: ty_variable:type().
-type cache() :: term(). %TODO


-define(LEAF, ty_rec).
-type type() :: {[variable()], ty_rec:type()}.

-spec unique(variable()) -> type().
unique(T) -> {[T], ty_rec:any()}.

% =============
% Subtyping
% =============

-spec is_empty(type(), S) -> {boolean(), S}.
is_empty({_Uniques, _Rec}, _ST) -> error(todo_emptiness).

% =============
% Tallying
% =============

% (NTLV rule)
-spec normalize(type(), monomorphic_variables(), S) -> {set_of_constraint_sets(), S}.
normalize(_T, _Fixed, _ST) -> error(todo_tally).

-spec all_variables(type(), cache()) -> sets:set(variable()).
all_variables(_T, _Cache) -> error(todo_all_variables).

% ops
-spec equal(type(), type()) -> boolean().
equal({U1, T1}, {U2, T2}) -> U1 == U2 andalso ty_rec:equal(T1, T2).

-spec compare(type(), type()) -> lt | gt | eq.
compare({U1, T1}, {U2, T2}) -> error(todo).

-spec any() -> type().
any() -> {[], ty_rec:any()}.

-spec empty() -> type().
empty() -> {[], ty_rec:empty()}.

-spec negate(type()) -> type().
negate({Uniques, Ty}) -> {Uniques, ty_rec:negate(Ty)}.

-spec intersect(type(), type()) -> type().
intersect({Uniques1, T1}, {Uniques2, T2}) -> {Uniques1 ++ Uniques2, ty_rec:intersect(T1, T2)}.

-spec union(type(), type()) -> type().
union({Uniques1, T1}, {Uniques2, T2}) -> error('???').

-spec difference(type(), type()) -> type().
difference({Uniques1, T1}, {Uniques2, T2}) -> error('???').

unparse(T, ST) -> error(todo).

assert_valid({_, TyRec}) -> ty_rec:assert_valid(TyRec).

% helper
-spec atom(dnf_ty_atom:type()) -> type().
atom(DnfTyAtom) -> {[], ?LEAF:atom(DnfTyAtom)}.
-spec interval(dnf_ty_interval:type()) -> type().
interval(DnfTyInterval) -> {[], ?LEAF:interval(DnfTyInterval)}.
-spec functions(ty_functions:type()) -> type().
functions(DnfTyFunctions) -> {[], ?LEAF:functions(DnfTyFunctions)}.
-spec tuples(ty_tuples:type()) -> type().
tuples(DnfTyTuples) -> {[], ?LEAF:tuples(DnfTyTuples)}.
-spec list(dnf_ty_list:type()) -> type().
list(DnfTyList) -> {[], ?LEAF:list(DnfTyList)}.
-spec predefined(dnf_ty_predefined:type()) -> type().
predefined(DnfTyPredef) -> {[], ?LEAF:predefined(DnfTyPredef)}.
-spec bitstring(dnf_ty_bitstring:type()) -> type().
bitstring(Dnf) -> {[], ?LEAF:bitstring(Dnf)}.
-spec map(dnf_ty_map:type()) -> type().
map(Dnf) -> {[], ?LEAF:map(Dnf)}.

% encoded map has to be a leaf during parsing
-spec tuple_to_map(type()) -> type().
tuple_to_map({T, Internal}) -> {T, ?LEAF:tuple_to_map(Internal)}.
