% bdd for variables
 
-export([get_full_dnf/1]).

-include("bdd.hrl").

substitute({terminal, X}, Map, Memo, _MkTy) ->
  {terminal, apply_to_node(X, Map, Memo)};
substitute({node, Var, Left, Right}, StdMap, Memo, MkTy) ->
  LSub = substitute(Left, StdMap, Memo, MkTy),
  RSub = substitute(Right, StdMap, Memo, MkTy),
  case maps:is_key(Var, StdMap) of
    true ->
      NewTy = maps:get(Var, StdMap),
      NewDnfVarTyAtom = MkTy(NewTy),
      union(
        intersect(NewDnfVarTyAtom, LSub),
        intersect(negate(NewDnfVarTyAtom), RSub)
      );
    _ ->
      union(
        intersect(var(Var), LSub),
        intersect(negate(var(Var)), RSub)
      )
  end
.

get_full_dnf(Ty) ->
  Dnf = get_dnf(Ty),
  % TODO technical dept, matching on literal '1' of type bdd_bool even though we can't know it's of type bdd_bool
  % as of yet, every second-level BDD uses bdd_bool as its terminal, so its OK
  lists:flatten([[{PosVar, NegVar, Pos, Neg} || {Pos, Neg, 1} <- ?TERMINAL:get_dnf(Dnfs)] || {PosVar, NegVar, Dnfs} <- Dnf]).