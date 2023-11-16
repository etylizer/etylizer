-module(ty_unf_map).

-define(OPT, optional).
-define(MAN, mandatory).

%% Typing Records, Maps and Structs, Theorem 4.2: union normal form

%% type operators
-export([struct_selection/2, map_selection/2, delete/2, update/3, concat/2]).

%% usual operations
-export([map/1, empty/0, any/0, b_union/2, b_intersect/2, b_diff/2]).

-type ty_map() :: term().
-type ty_ref() :: {ty_ref, integer()}.
-type ty_unf_map() :: [ty_map()].

-spec map(ty_map()) -> ty_unf_map().
map(TyMap) -> [TyMap].

-spec struct_selection(ty_map:l(), ty_unf_map()) -> {ty_map:assoc(), ty_ref()}.
struct_selection(L, U) ->
  {Associations, Projections} = lists:unzip([ty_map:pi(L, X) || X <- U]),
  case lists:any(fun(A) -> A == ?OPT end, Associations) of
    true -> {?OPT, u(Projections)};
    false -> {?MAN, u(Projections)}
  end.

-spec map_selection(ty_ref(), ty_unf_map()) -> {ty_map:assoc(), ty_ref()}.
map_selection(Ty, U) ->
  {_, DnfAtom, DnfInt, _, DnfTuple, _, _} = ty_rec:pi_all(Ty),
  EA = dnf_var_ty_atom:is_empty(DnfAtom),
  EI = dnf_var_int:is_empty(DnfInt),
  ET = dnf_var_ty_tuple:is_empty(DnfTuple),
  AtomProj = case EA of false -> [ty_map:pi_tag(atom_key, X) || X <- U]; true -> [] end,
  IntProj = case EI of false -> [ty_map:pi_tag(integer_key, X) || X <- U]; true -> [] end,
  TupleProj = case ET of false -> [ty_map:pi_tag(tuple_key, X) || X <- U]; true -> [] end,

  {?OPT, u(AtomProj ++ IntProj ++ TupleProj)}.

-spec delete(ty_ref(), ty_unf_map()) -> ty_unf_map().
delete(_, _) -> todo.

-spec update(ty_ref(), ty_ref(), ty_unf_map()) -> ty_unf_map().
update(_, _, _) -> todo.

-spec concat(ty_unf_map(), ty_unf_map()) -> ty_unf_map().
concat(_, _) -> todo.

empty() -> [].
any() -> [ty_map:b_anymap()].

b_union(U1, U2) -> U1 ++ U2.

b_intersect([], _) -> [];
b_intersect(_, []) -> [];
b_intersect([X | Xs] = U1, U2 = [Y | Ys]) ->
  {ty_map, LsInt, _} = Z = ty_map:b_intersect(X, Y),
  case labels_empty(LsInt) of % steps always at least include ⊥, only labels could be empty
    true -> [];
    false -> [Z]
  end
  ++ b_intersect(U1, Ys) ++ b_intersect(Xs, U2).

b_diff([], _) -> [];
b_diff(U, []) -> U;
b_diff([X | Xs] = U1, U2 = [Y | Ys]) ->
  {ty_map, LsX, StX} = X,
  {ty_map, LsDiff, StDiff} = ty_map:b_diff(X, Y),
  L = ty_map:map(LsX, StDiff),
  R = [ty_map:map(LsX#{AL => TyRef}, StX) || AL := TyRef <- LsDiff, not field_empty(AL, TyRef)],
  case steps_empty(StDiff) of % steps could be empty s.t. they don't include ⊥
    true -> R;
    false -> [L | R]
  end
  ++ b_diff(U1, Ys) ++ b_diff(Xs, U2).

labels_empty(Ls) -> lists:max([field_empty(AL, TyRef) || AL := TyRef <- Ls], false).
steps_empty(St) -> lists:all(fun ty_rec:is_empty/1, maps:values(St)).
field_empty({A, _L}, TyRef) -> ?MAN == A andalso ty_rec:is_empty(TyRef).
u(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).
