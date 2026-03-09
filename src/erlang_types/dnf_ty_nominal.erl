-module(dnf_ty_nominal).

%% BDD layer for nominal type tags.
%% Sits between dnf_ty_variable (above) and ty_rec (below).
%% Atoms are ty_nominal (nominal tags), leaves are ty_rec (structural types).

-export([
  is_literal_empty/1,
  tuple_to_map/1,
  nominal/2
]).

-define(ATOM, ty_nominal).
-define(LEAF, ty_rec).

-include("dnf/bdd.hrl").

%% ===== Additional exports beyond bdd.hrl =====

-spec is_literal_empty(type()) -> boolean().
is_literal_empty(Bdd) -> Bdd =:= empty().

-spec tuple_to_map(type()) -> type().
tuple_to_map({leaf, Internal}) -> {leaf, ty_rec:tuple_to_map(Internal)};
tuple_to_map({node, Tag, Pos, Neg}) -> {node, Tag, tuple_to_map(Pos), tuple_to_map(Neg)}.

%% Wrap a dnf_ty_nominal BDD with a nominal tag.
-spec nominal(ty_nominal:type(), type()) -> type().
nominal(NomTag, NomBdd) ->
  intersect(singleton(NomTag), NomBdd).

%% ===== BDD callbacks =====

%% Subtyping: is_empty_line
%%
%% A DNF line at the nominal level has:
%%   AllPos = list of positive nominal tags
%%   Neg = list of negative nominal tags
%%   T = ty_rec leaf (structural type)
%%
%% The line is empty if:
%%   1. The structural leaf is empty
%%   2. Two+ positive tags are mutually exclusive (neither derives from the other)
%%   3. Nominal compatibility: no positive tags + some negative tags (structural <: nominal),
%%      or every negative tag's body contains some positive tag (derivation upcast)

-spec is_empty_line({[T], [T], ?LEAF:type()}, S) -> {boolean(), S} when S :: is_empty_cache(), T :: ?ATOM:type().
is_empty_line({AllPos, Neg, T}, ST) ->
  case nominal_line_is_compatible(AllPos, Neg) of
    true -> {true, ST};
    false -> ty_rec:is_empty(T, ST)
  end.

%% Tallying: normalize_line
%%
%% At this level there are no type variables. All atoms are nominal tags
%% which are effectively "delta" (fixed). We check nominal compatibility
%% and otherwise delegate to ty_rec:normalize for structural checking.

-spec normalize_line({[T], [T], ?LEAF:type()}, monomorphic_variables(), S) ->
    {set_of_constraint_sets(), S} when S :: normalize_cache(), T :: ?ATOM:type().
normalize_line({[], [], TyRec}, Fixed, ST) ->
  ty_rec:normalize(TyRec, Fixed, ST);
normalize_line({PVar, NVar, TyRec}, Fixed, ST) ->
  case nominal_line_is_compatible(PVar, NVar) of
    true -> {constraint_set:sat(), ST};
    false -> ty_rec:normalize(TyRec, Fixed, ST)
  end.

%% Variables: all_variables_line
%%
%% No variables at this level. Delegate to ty_rec.

-spec all_variables_line([T], [T], ?LEAF:type(), all_variables_cache()) -> sets:set(variable()) when T :: ?ATOM:type().
all_variables_line(_P, _N, Leaf, Cache) ->
  ty_rec:all_variables(Leaf, Cache).

%% ===== Nominal logic =====

%% Check if a DNF line's nominal tags make the line empty.
%% Returns true (= line is empty) if:
%% - Two+ positive tags are mutually exclusive (neither derives from the other)
%% - No positive tags + some negative tags (structural <: nominal compatibility)
%% - Every negative tag's body contains some positive tag (derivation upcast)
-spec nominal_line_is_compatible([?ATOM:type()], [?ATOM:type()]) -> boolean().
nominal_line_is_compatible(AllPos, Neg) ->
  PosKeys = [ty_nominal:key(A) || A <- AllPos],
  NegKeys = [ty_nominal:key(A) || A <- Neg],
  case {PosKeys, NegKeys} of
    {[_|_], []} ->
      % Only positive tags, no negative: check mutual exclusion
      has_incompatible_pair(PosKeys);
    {[], [_|_]} ->
      % Only negative tags: structural <: nominal, always compatible
      true;
    {[_|_], [_|_]} ->
      % Both positive and negative: check mutual exclusion among positives,
      % or derivation compatibility between positive and negative
      has_incompatible_pair(PosKeys) orelse
      lists:all(fun(NegKey) ->
        lists:any(fun(PosKey) ->
          ty_parser:nominal_derives_from(NegKey, PosKey)
        end, PosKeys)
      end, NegKeys);
    {[], []} ->
      false
  end.

-spec has_incompatible_pair([ty_nominal:nominal_key()]) -> boolean().
has_incompatible_pair([]) -> false;
has_incompatible_pair([K | Rest]) ->
  lists:any(fun(K2) ->
    not ty_parser:nominal_derives_from(K, K2) andalso
    not ty_parser:nominal_derives_from(K2, K)
  end, Rest) orelse has_incompatible_pair(Rest).
