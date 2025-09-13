-module(ty_unit).

% Units are disjunctions of tag1 /\.../\ tagN /\ ty_rec.
% This intersection enables unique types when tags are distinct.
% Tags are variables but a unit is not decomposable into its tags.

-export([
  unit/1,
  unit/2,
  equal/2,
  compare/2,
  any/0,
  empty/0,
  union/2,
  intersect/2,
  difference/2,
  negate/1,

  is_empty/2,
  is_literal_empty/1,
  normalize/3,
  all_variables/2,
  reorder/1,
  assert_valid/1,
  unparse/2
]).

-export_type([type/0]).

-type monomorphic_variables() :: etally:monomorphic_variables().
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type ast_ty() :: ast:ty().
-type ty_rec() :: ty_rec:type().
-type variable() :: ty_variable:type().
-type cache() :: term(). %TODO

-opaque type() :: nonempty_list(conjunct()). % dnf
-type conjunct() :: {[tag()], [tag()], ty_rec()}.
-type tag() :: ty_variable:type().

-spec unit(ty_rec()) -> type().
unit(Rec) -> [{[], [], Rec}].

-spec unit(tag(), ty_rec()) -> type().
unit(Tag, Rec) -> [{[Tag], [], Rec}].

-spec any() -> type().
any() -> unit(ty_rec:any()).

-spec empty() -> type().
empty() -> unit(ty_rec:empty()).

-spec equal(type(), type()) -> boolean().
equal(Ty1, Ty2) -> compare(Ty1, Ty2) == eq.

-spec compare(type(), type()) -> lt | gt | eq.
compare(Ty1, Ty2) ->
  Cmp = fun({_, _, Rec1}, {_, _, Rec2}) -> ty_rec:compare(Rec1, Rec2) end,
  utils:compare(Cmp,
    lists:sort(fun(C1, C2) -> Cmp(C1, C2) /= gt end, Ty1),
    lists:sort(fun(C1, C2) -> Cmp(C1, C2) /= gt end, Ty2)
  ).

% =============
% Subtyping
% =============

-spec is_empty(type(), S) -> {boolean(), S}.
is_empty([{PTags, NTags, Rec}], ST) ->
  TagConflict = lists:any(fun(T) -> lists:member(T, PTags) end, NTags),
  case TagConflict of
    true -> {true, ST};
    false -> ty_rec:is_empty(Rec, ST)
  end;
is_empty([Conj | Conjuncts], ST) ->
  case is_empty([Conj], ST) of
    {true, ST2} -> is_empty(Conjuncts, ST2);
    {false, ST2} -> {false, ST2}
  end.

-spec is_literal_empty(type()) -> boolean().
is_literal_empty([{_, _, Rec}]) -> ty_rec:is_literal_empty(Rec);
is_literal_empty([Conj | Conjuncts]) -> is_literal_empty([Conj]) andalso is_literal_empty(Conjuncts).

% =============
% Tallying
% =============

-spec normalize(type(), monomorphic_variables(), S) -> {set_of_constraint_sets(), S}.
normalize([{PTags, NTags, Rec}], Fixed, ST) ->
  TagConflict = lists:any(fun(T) -> lists:member(T, PTags) end, NTags),
  case TagConflict of
    true -> {[[]], ST};
    false -> ty_rec:normalize(Rec, Fixed, ST)
  end;
normalize([Conj | Conjuncts], Fixed, ST) ->
  {CSet1, ST1} = normalize([Conj], Fixed, ST),
  {CSet2, ST2} = normalize(Conjuncts, Fixed, ST1),
  {constraint_set:meet(CSet1, CSet2, Fixed), ST2}.

-spec all_variables(type(), cache()) -> sets:set(variable()).
all_variables(Ty, Cache) ->
  % discard tags: they do not count as "occurring" variables
  sets:union([ty_rec:all_variables(Rec, Cache) || {_, _, Rec} <- Ty]).

% ops

-spec negate(type()) -> type().
negate([{PTags, NTags, Rec}]) ->
  Ty1 = [{[], [T], ty_rec:any()} || T <- PTags],
  Ty2 = [{[T], [], ty_rec:any()} || T <- NTags],
  Ty3 = [{[], [], ty_rec:negate(Rec)}],
  union(Ty1, union(Ty2, Ty3));
negate([Conj | Conjuncts]) ->
  intersect(negate([Conj]), negate(Conjuncts)).

-spec intersect(type(), type()) -> type().
intersect(Ty1, Ty2) ->
  _Ty3 = [
    {PTags1 ++ PTags2, NTags1 ++ NTags2, ty_rec:intersect(Rec1, Rec2)}
    || {PTags1, NTags1, Rec1} <- Ty1,
       {PTags2, NTags2, Rec2} <- Ty2
  ].

-spec union(type(), type()) -> type().
union(Ty1, Ty2) -> Ty1 ++ Ty2.

-spec difference(type(), type()) -> type().
difference(Ty1, Ty2) -> intersect(Ty1, negate(Ty2)).

-spec reorder(type()) -> type().
reorder(Ty) ->
  [{PTags, NTags, ty_rec:reorder(Rec)} || {PTags, NTags, Rec} <- Ty].

-spec assert_valid(type()) -> _.
assert_valid(Ty) ->
  lists:foreach(fun({_, _, Rec}) -> ty_rec:assert_valid(Rec) end, Ty).

-spec unparse(type(), S) -> {ast_ty(), S}.
unparse(Ty, ST) ->
  UParseTag = fun(T, {Ast, ST0}) -> {Ast1, ST1} = ty_variable:unparse(T, ST0), {ast_lib:mk_intersection([Ast1, Ast]), ST1} end,
  UParseRec = fun(Rec, ST0) -> {Ast, ST1} = ty_rec:unparse(Rec, ST0), {Ast, ST1} end,
  UParseConjunct =
    fun({PTags, NTags, Rec}, {Ast, ST0}) ->
      {Ast1, ST1} = lists:foldr(UParseTag, {stdtypes:any(), ST0}, PTags),
      {Ast2, ST2} = lists:foldr(UParseTag, {stdtypes:any(), ST1}, NTags),
      {Ast3, ST3} = UParseRec(Rec, ST2),
      Ast4 = ast_lib:mk_intersection([Ast1, Ast2, Ast3]),
      {ast_lib:mk_union([Ast4, Ast]), ST3}
    end,
  lists:foldr(UParseConjunct, {stdtypes:empty(), ST}, Ty).