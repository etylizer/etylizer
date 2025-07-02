-module(dnf_ty_map).

-define(ATOM, ty_map).
-define(LEAF, ty_bool).

-include("dnf/bdd.hrl").

-spec is_empty_line({[T], [T], ?LEAF:type()}, S) -> {boolean(), S} when T :: ?ATOM:type().
is_empty_line({[], [], _T}, _ST) -> error(todo);
is_empty_line({[], Neg = [_ | _], T}, ST) ->
  % this is the special case on why we can't use is_empty_line of dnf_ty_tuple directly
  % the 'any' representation is different
  P1 = ty_node:make(dnf_ty_variable:tuples(ty_tuples:singleton(2, dnf_ty_tuple:any()))),
  P2 = ty_node:make(dnf_ty_variable:functions(ty_functions:singleton(2, dnf_ty_function:any()))),
  PPos = ty_tuple:tuple([P1, P2]),
  is_empty_line({[PPos], Neg, T}, ST);
is_empty_line({Pos, Neg, T}, ST) ->
  T = ?LEAF:any(), % sanity
  BigS = ty_tuple:big_intersect(Pos),
  dnf_ty_tuple:phi(ty_tuple:components(BigS), Neg, ST).

-spec normalize_line({[T], [T], ?LEAF:type()}, monomorphic_variables(), S) -> {set_of_constraint_sets(), S} when T :: ?ATOM:type().
normalize_line({[], [], _T}, _Fixed, _ST) -> error(todo);
normalize_line({[], Neg = [_ | _], T}, Fixed, ST) ->
  % TODO test case for tally map for this branch
  P1 = ty:tuples(ty_tuples:singleton(2, dnf_ty_tuple:any())),
  P2 = ty:functions(ty_functions:singleton(2, dnf_ty_function:any())),
  PPos = ty_map:map(P1, P2),
  normalize_line({[PPos], Neg, T}, Fixed, ST);
normalize_line({Pos, Neg, T}, Fixed, ST) ->
  T = ?LEAF:any(), % sanity
  BigS = ty_tuple:big_intersect(Pos),
  dnf_ty_tuple:phi_norm(ty_tuple:components(BigS), Neg, Fixed, ST).

-spec all_variables_line([T], [T], ?LEAF:type(), cache()) -> sets:set(variable()) when T :: ?ATOM:type().
all_variables_line(P, N, L, Cache) ->
  dnf_ty_tuple:all_variables_line(P, N, L, Cache).
