-module(dnf_ty_variable).

-compile([export_all, nowarn_export_all]).

-define(ATOM, ty_variable).
-define(LEAF, ty_rec).
% -define(NODE, ty_node).

-include("dnf/bdd.hrl").

-type type() :: any(). % TODO
% -spec function(ty_function()) -> dnf_ty_function().
% function(TyFunction) -> node(TyFunction).

% -> {boolean(), local_cache()}.
is_empty_line({AllPos, Neg, T}, ST) ->
  case {AllPos, Neg, ?LEAF:is_literal_empty(T)} of
    {_, _, true} -> 
      {true, ST};
    {_PositiveVariables, _NegativeVariables, false} -> % ignore variables for emptiness
      ?LEAF:is_empty(T, ST)
  end.

% helper constructors (used by ty_parser)
atom(DnfTyAtom) -> leaf(ty_rec:atom(DnfTyAtom)).
interval(DnfTyInterval) -> leaf(ty_rec:interval(DnfTyInterval)).
functions(DnfTyFunctions) -> leaf(ty_rec:functions(DnfTyFunctions)).
tuples(DnfTyTuples) -> leaf(ty_rec:tuples(DnfTyTuples)).
list(DnfTyList) -> leaf(ty_rec:list(DnfTyList)).
predefined(DnfTyPredef) -> leaf(ty_rec:predefined(DnfTyPredef)).
bitstring(Dnf) -> leaf(ty_rec:bitstring(Dnf)).
map(Dnf) -> leaf(ty_rec:map(Dnf)).

% encoded map has to be a leaf during parsing
tuple_to_map({leaf, Internal}) -> {leaf, ty_rec:tuple_to_map(Internal)}.

% =============
% Tallying
% =============

% (NTLV rule)
normalize_line({[], [], TyRec}, Fixed, ST) ->
  ty_rec:normalize(TyRec, Fixed, ST);
normalize_line({PVar, NVar, TyRec}, Fixed, ST) ->
  %io:format(user, "Normalizing ~p~n", [Line]),
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

% assumption: PVars U NVars is not empty
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

all_variables_line(P, N, Leaf, Cache) ->
  sets:union([sets:from_list(P),
              sets:from_list(N),
              ty_rec:all_variables(Leaf, Cache)
             ]).
