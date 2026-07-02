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

-export([
  substitute/3
]).

-define(ATOM, ty_variable).
-define(LEAF, ty_rec).

-include("dnf/bdd.hrl").

% helper constructors (used by ty_parser)
-spec atom(dnf_ty_atom:type()) -> bdd().
atom(DnfTyAtom) -> leaf(ty_rec:atom(DnfTyAtom)).
-spec interval(dnf_ty_interval:type()) -> bdd().
interval(DnfTyInterval) -> leaf(ty_rec:interval(DnfTyInterval)).
-spec functions(ty_functions:type()) -> bdd().
functions(DnfTyFunctions) -> leaf(ty_rec:functions(DnfTyFunctions)).
-spec tuples(ty_tuples:type()) -> bdd().
tuples(DnfTyTuples) -> leaf(ty_rec:tuples(DnfTyTuples)).
-spec list(dnf_ty_list:type()) -> bdd().
list(DnfTyList) -> leaf(ty_rec:list(DnfTyList)).
-spec predefined(dnf_ty_predefined:type()) -> bdd().
predefined(DnfTyPredef) -> leaf(ty_rec:predefined(DnfTyPredef)).
-spec bitstring(dnf_ty_bitstring:type()) -> bdd().
bitstring(Dnf) -> leaf(ty_rec:bitstring(Dnf)).
-spec map(dnf_ty_map:type()) -> bdd().
map(Dnf) -> leaf(ty_rec:map(Dnf)).

% encoded map has to be a leaf during parsing
-spec tuple_to_map(leaf()) -> leaf().
tuple_to_map({leaf, Internal}) -> {leaf, ty_rec:tuple_to_map(Internal)}.

% =============
% Subtyping
% =============

-spec is_empty_line({[T], [T], ?LEAF:type()}, S) -> {boolean(), S} when S :: is_empty_cache(), T :: ?ATOM:type().
is_empty_line({AllPos, Neg, T}, ST) ->
  case {AllPos, Neg, ty_rec:is_literal_empty(T)} of
    {_, _, true} -> 
      {true, ST};
    {_PositiveVariables, _NegativeVariables, false} -> % ignore variables for emptiness
      ty_rec:is_empty(T, ST)
  end.

% =============
% Tallying
% =============

% (NTLV rule)
-spec normalize_line({[T], [T], ?LEAF:type()}, monomorphic_variables(), S) -> 
    {set_of_constraint_sets(), S} when S :: normalize_cache(),T :: ?ATOM:type().
normalize_line({[], [], TyRec}, Fixed, ST) ->
  ty_rec:normalize(TyRec, Fixed, ST);
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
      ty_rec:normalize(TyRec, Fixed, ST)
  end.

% assumption: PVars U NVars is not empty
-type tagged_variable() :: {pos | neg | {delta, pos | neg}, ?ATOM:type()}.
-spec smallest([T], [T], monomorphic_variables()) -> 
    {tagged_variable(), [tagged_variable()]} when T :: ?ATOM:type().
smallest(PositiveVariables, NegativeVariables, FixedVariables) ->
  ?assert_pattern(true, (length(PositiveVariables) + length(NegativeVariables)) > 0),

  % fixed variables are higher order than all non-fixed ones, will be picked last
  PositiveVariablesTagged = [{pos, V} || V <- PositiveVariables, not maps:is_key(V, FixedVariables)],
  NegativeVariablesTagged = [{neg, V} || V <- NegativeVariables, not maps:is_key(V, FixedVariables)],

  RestTagged =
    [{{delta, neg}, V} || V <- NegativeVariables, maps:is_key(V, FixedVariables)] ++
    [{{delta, pos}, V} || V <- PositiveVariables, maps:is_key(V, FixedVariables)],

  %% A5 swing: pick the LARGEST variable first (reverse the usual lex order)
  %% — fpos already placed the most-discriminating vars at one end via the
  %% reorder, and reversing the picker swaps which end we resolve first. Can
  %% materially change the recursion-tree shape.
  Sort = case os:getenv("ETY_PICKER_REV") of
    "1" -> fun({_, V}, {_, V2}) -> not ty_variable:leq(V, V2) end;
    _   -> fun({_, V}, {_, V2}) -> ty_variable:leq(V, V2) end
  end,
  [X | Z] =
  ?assert_pattern([_ | _],
                  lists:sort(Sort, PositiveVariablesTagged++NegativeVariablesTagged) ++
                  lists:sort(Sort, RestTagged)),

  {X, Z}.

-spec single(boolean(), [T], [T], ?LEAF:type()) -> bdd() when T :: ?ATOM:type().
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

-spec all_variables_line([T], [T], ?LEAF:type(), all_variables_cache()) -> sets:set(variable()) when T :: ?ATOM:type().
all_variables_line(P, N, Leaf, Cache) ->
  sets:union([sets:from_list(P),
              sets:from_list(N),
              ty_rec:all_variables(Leaf, Cache)
             ]).

% =============
% Substitution
% =============
% Substitute variables (Sigma) and node references (NodeMap) in this BDD.
% Sigma maps a ty_variable to a ty_node whose body will replace the variable.
% NodeMap maps existing ty_nodes (referenced in leaves) to new ty_nodes.
-spec substitute(bdd(), #{variable() => ty_node:type()}, #{ty_node:type() => ty_node:type()}) -> bdd().
substitute({leaf, TyRec}, _Sigma, NodeMap) ->
  {leaf, ty_rec:substitute(TyRec, NodeMap)};
substitute({node, Var, P, N}, Sigma, NodeMap) ->
  P2 = substitute(P, Sigma, NodeMap),
  N2 = substitute(N, Sigma, NodeMap),
  case maps:find(Var, Sigma) of
    {ok, TNode} ->
      % Var maps to a type. Load its BDD (a dnf_ty_variable BDD) and combine via cap/diff/cup.
      TBdd = ty_node:load(TNode),
      union(intersect(TBdd, P2), difference(N2, TBdd));
    error ->
      % Var is unchanged; rebuild with substituted children.
      % Since Var's position in ordering is unchanged, this remains a valid BDD
      % as long as P2 and N2 are valid (which they are recursively).
      VBdd = singleton(Var),
      union(intersect(VBdd, P2), difference(N2, VBdd))
  end.
