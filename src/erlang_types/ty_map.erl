-module(ty_map).

%% Implements unrestricted maps through relation x function interpretation.

-export([map/2, empty/0, any/0, emptymap/0, intersect/2]).
-export([compare/2, equal/2, has_ref/2, substitute/3, transform/2, all_variables/1]).

-type ty_map() :: {ty_map, relation(), overloaded_function()}.
-type relation() :: dnf_ty_tuple().
-type overloaded_function() :: dnf_ty_function().

-type dnf_ty_tuple() :: term().
-type dnf_ty_function() :: term().

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.
equal(P1, P2) -> compare(P1, P2) =:= 0.

-spec map(relation(), overloaded_function()) -> ty_map().
map(Tup, Fun) -> {ty_map, Tup, Fun}.

-spec empty() -> ty_map().
empty() -> map(dnf_ty_tuple:empty(), dnf_ty_function:empty()).

-spec any() -> ty_map().
any() -> map(dnf_ty_tuple:any(), dnf_ty_function:any()).

-spec emptymap() -> ty_map().
emptymap() -> map(dnf_ty_tuple:empty(), dnf_ty_function:any()).

-spec intersect(ty_map(), ty_map()) -> ty_map().
intersect({ty_map, Tup1, Fun1}, {ty_map, Tup2, Fun2}) ->
  map(
    dnf_ty_tuple:intersect(Tup1, Tup2),
    dnf_ty_function:intersect(Fun1, Fun2)).

has_ref({ty_map, Tup, Fun}, Ref) ->
  dnf_ty_tuple:has_ref(Tup, Ref)
    orelse dnf_ty_function:has_ref(Fun, Ref).

substitute({ty_map, Tup, Fun}, SubstituteMap, Memo) ->
  {ty_map,
    dnf_ty_tuple:apply_to_node(Tup, SubstituteMap, Memo),
    dnf_ty_function:apply_to_node(Fun, SubstituteMap, Memo)
  }.

transform({ty_map, Tup, Fun}, #{to_map := ToMap}) ->
  DnfTup = dnf_ty_tuple:get_dnf(Tup),
  DnfFun = dnf_ty_function:get_dnf(Fun),
  Optional = lists:flatten([transform_tuple_coclause(Pos, Neg, T) || {Pos, Neg, T} <- DnfTup]),
  Mandatory = lists:flatten([transform_function_coclause(Pos, Neg, T) || {Pos, Neg, T} <- DnfFun]),
  ToMap(Optional, Mandatory).


transform_tuple_coclause(Pos, [], T) ->
  case bdd_bool:empty() of
    T -> [];
    _ -> [begin
            [K, V] = ty_tuple:components(TyTuple),
            {K, V}
          end || TyTuple <- Pos]
  end;
transform_tuple_coclause(_, _Neg, _) -> error(illegal_state).


transform_function_coclause(Pos, [], T) ->
  case bdd_bool:empty() of
    T -> [];
    _ -> [begin
            [K] = ty_function:domains(TyFun),
            {K, ty_function:codomain(TyFun)}
          end || TyFun <- Pos]
  end;
transform_function_coclause(_, _Neg, _) -> error(illegal_state).


all_variables({ty_map, Tup, Fun}) ->
  dnf_ty_tuple:all_variables(Tup)
  ++ dnf_ty_function:all_variables(Fun).