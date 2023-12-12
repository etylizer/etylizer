% bdd for variables

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