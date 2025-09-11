-module(dnf_ty_variable).

% helper constructors
-export([
  atom/1,
  interval/1,
  functions/1,
  tuples/1,
  list/1,
  predefined/1,
  bitstring/1,
  map/1
]).

-export([
  tuple_to_map/1
]).

-define(ATOM, ty_variable).
-define(LEAF, ty_unique).

-include("dnf/bdd.hrl").

% helper constructors (used by ty_parser)
-spec atom(dnf_ty_atom:type()) -> bdd().
atom(DnfTyAtom) -> leaf(?LEAF:atom(DnfTyAtom)).
-spec interval(dnf_ty_interval:type()) -> bdd().
interval(DnfTyInterval) -> leaf(?LEAF:interval(DnfTyInterval)).
-spec functions(ty_functions:type()) -> bdd().
functions(DnfTyFunctions) -> leaf(?LEAF:functions(DnfTyFunctions)).
-spec tuples(ty_tuples:type()) -> bdd().
tuples(DnfTyTuples) -> leaf(?LEAF:tuples(DnfTyTuples)).
-spec list(dnf_ty_list:type()) -> bdd().
list(DnfTyList) -> leaf(?LEAF:list(DnfTyList)).
-spec predefined(dnf_ty_predefined:type()) -> bdd().
predefined(DnfTyPredef) -> leaf(?LEAF:predefined(DnfTyPredef)).
-spec bitstring(dnf_ty_bitstring:type()) -> bdd().
bitstring(Dnf) -> leaf(?LEAF:bitstring(Dnf)).
-spec map(dnf_ty_map:type()) -> bdd().
map(Dnf) -> leaf(?LEAF:map(Dnf)).

% encoded map has to be a leaf during parsing
-spec tuple_to_map(leaf()) -> leaf().
tuple_to_map({leaf, Internal}) -> {leaf, ?LEAF:tuple_to_map(Internal)}.

% =============
% Subtyping
% =============

-spec is_empty_line({[T], [T], ?LEAF:type()}, S) -> {boolean(), S} when T :: ?ATOM:type().
is_empty_line({AllPos, Neg, T}, ST) ->
  case {AllPos, Neg, ?LEAF:is_literal_empty(T)} of
    {_, _, true} -> 
      {true, ST};
    {_PositiveVariables, _NegativeVariables, false} -> % ignore variables for emptiness
      ?LEAF:is_empty(T, ST)
  end.

% =============
% Tallying
% =============

% (NTLV rule)
-spec normalize_line({[T], [T], ?LEAF:type()}, monomorphic_variables(), S) -> {set_of_constraint_sets(), S} when T :: ?ATOM:type().
normalize_line({[], [], TyRec}, Fixed, ST) ->
  ?LEAF:normalize(TyRec, Fixed, ST);
normalize_line({PVar, NVar, TyRec}, Fixed, ST) ->
  SmallestVar = smallest(PVar, NVar, Fixed),
  %io:format(user, "Got smallest var ~p~n", [SmallestVar]),
  case SmallestVar of
    {{pos, Var}, _Others} ->
      Singled = single(true, PVar -- [Var], NVar, TyRec ),
      %io:format(user, "Singled ~p~n", [Singled]),
      {[[{Var, ty_node:empty(), ty_node:make(Singled)}]], ST};
    {{neg, Var}, _Others} ->
      Singled = single(false, PVar, NVar -- [Var], TyRec),
      %io:format(user, "Singled ~p~n", [Singled]),
      {[[{Var, ty_node:make(Singled), ty_node:any()}]], ST};
    {{{delta, _}, _}, _} ->
      % part 1 paper Lemma C.3 and C.11 all fixed variables can be eliminated
      ?LEAF:normalize(TyRec, Fixed, ST)
  end.

% assumption: PVars U NVars is not empty
-type tagged_variable() :: {pos | neg | {delta, pos | neg}, ?ATOM:type()}.
-spec smallest([T], [T], monomorphic_variables()) -> {tagged_variable(), [tagged_variable()]}.
smallest(PositiveVariables, NegativeVariables, FixedVariables) ->
  true = (length(PositiveVariables) + length(NegativeVariables)) > 0,

  % fixed variables are higher order than all non-fixed ones, will be picked last
  PositiveVariablesTagged = [{pos, V} || V <- PositiveVariables, not maps:is_key(V, FixedVariables)],
  NegativeVariablesTagged = [{neg, V} || V <- NegativeVariables, not maps:is_key(V, FixedVariables)],

  RestTagged =
    [{{delta, neg}, V} || V <- NegativeVariables, maps:is_key(V, FixedVariables)] ++
    [{{delta, pos}, V} || V <- PositiveVariables, maps:is_key(V, FixedVariables)],

  Sort = fun({_, V}, {_, V2}) -> ty_variable:leq(V, V2) end,
  [X | Z] = lists:sort(Sort, PositiveVariablesTagged++NegativeVariablesTagged) ++ lists:sort(Sort, RestTagged),

  {X, Z}.

-spec single(boolean(), [T], [T], ?LEAF:type()) -> bdd().
single(Pol, VPos, VNeg, Ty) ->
  AccP = lists:foldl(fun(Var, TTy) -> 
    VVar = dnf_ty_variable:singleton(Var),
    intersect(TTy, VVar) 
  end, leaf(Ty), VPos),

  AccN = lists:foldl(fun(Var, TTy) -> 
    VVar = dnf_ty_variable:singleton(Var),
    union(TTy, VVar) 
  end, empty(), VNeg),

  S = difference(AccP, AccN),
  case Pol of
    true -> negate(S);
    _ -> S
  end.

-spec all_variables_line([T], [T], ?LEAF:type(), cache()) -> sets:set(variable()) when T :: ?ATOM:type().
all_variables_line(P, N, Leaf, Cache) ->
  sets:union([sets:from_list(P),
              sets:from_list(N),
              ?LEAF:all_variables(Leaf, Cache)
             ]).
