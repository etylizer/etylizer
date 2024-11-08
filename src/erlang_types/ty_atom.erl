-module(ty_atom).

%% Efficient atom representation
-export([compare/2, equal/2]).
-export([empty/0, any/0]).
-export([union/2, intersect/2, diff/2, negate/1, is_any/1]).
-export([is_empty/1]).
-export([transform/2, raw_transform/2]).
-export([finite/1, cofinite/1]).
-export([has_ref/2, to_singletons/1, normalize_corec/5, substitute/4, all_variables/2]).

-export([hash/1, s_is_empty/1]).
hash(Atom) -> erlang:phash2(Atom). %TODO custom hash function
s_is_empty(Atom) -> is_empty(Atom).

has_ref(_, _) -> false.
all_variables(_, _) -> [].
substitute(_, Ty, _, _) -> Ty.

to_singletons({Atoms, finite}) -> [ty_rec:atom(dnf_var_ty_atom:ty_atom(finite([A]))) || A <- gb_sets:to_list(Atoms)];
to_singletons({_, cofinite}) -> error(illegal_state).

transform({Atoms, finite}, #{to_atom := ToAtom, union := Union}) ->
  Union(lists:map(fun(A) -> ToAtom(A) end, gb_sets:to_list(Atoms)));
transform({Atoms, cofinite}, #{to_atom := ToAtom, union := Union, negate := Negate}) ->
  Negate(Union(lists:map(fun(A) -> ToAtom(A) end, gb_sets:to_list(Atoms)))).

raw_transform(T, Op) -> transform(T, Op).

empty() -> {{0, nil}, finite}.
any() -> {{0, nil}, cofinite}.

finite([]) ->
  any();
finite([X | Xs]) ->
  intersect({gb_sets:from_list([X]), finite}, finite(Xs)).
cofinite(ListOfBasic) -> {gb_sets:from_list(ListOfBasic), cofinite}.

negate({S, finite}) -> {S, cofinite};
negate({S, cofinite}) -> {S, finite}.

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

union(S,T) -> negate(intersect(negate(S), negate(T))).

diff(S,T) -> intersect(S, negate(T)).

equal({_, finite},{_, cofinite}) -> false;
equal({_, cofinite},{_, finite}) -> false;
equal({S, _}, {T, _}) -> gb_sets:is_subset(S,T) andalso gb_sets:is_subset(T,S).

is_empty(Rep) ->
  case Rep of
    {{0, nil}, finite} -> true;
    _ -> false
  end.

is_any(Rep) ->
  case Rep of
    {{0, nil}, cofinite} -> true;
    _ -> false
  end.

% using erlang total ordering for now
compare(R1, R2) -> case R1 < R2 of true -> -1; _ -> case R1 > R2 of true -> 1; _ -> 0 end end.

normalize_corec(TyAtom, [], [], _Fixed, _) ->
  % Fig. 3 Line 3
  case is_empty(TyAtom) of
    true -> [[]];
    false -> []
  end;
normalize_corec(TyAtom, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:atom(dnf_var_ty_atom:ty_atom(TyAtom)),
  % ntlv rule
  ty_variable:normalize_corec(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:atom(dnf_var_ty_atom:var(Var)) end, M).


