% bdd for variables

-include("bdd.hrl").

substitute(_Ref = {bdd_ref, 0}, _Map, _Memo, _) -> empty();
substitute(Ref = {bdd_ref, _}, Map, Memo, MkTy) ->
  #{Ref := A} = get_memory(),
  substitute(A, Map, Memo, MkTy);
substitute({terminal, X}, Map, Memo, _MkTy) ->
  mk_terminal(apply_to_node(X, Map, Memo));
substitute({node, Var, Left, Right}, StdMap, Memo, MkTy) ->
  LSub = substitute(Left, StdMap, Memo, MkTy),
  is_ref(LSub),
  RSub = substitute(Right, StdMap, Memo, MkTy),
  is_ref(RSub),
  case maps:is_key(Var, StdMap) of
    true ->
      NewTy = maps:get(Var, StdMap),
      NewDnfVarTyAtom = MkTy(NewTy),
      is_ref(NewDnfVarTyAtom),
      union(
        intersect(NewDnfVarTyAtom, LSub),
        intersect(negate(NewDnfVarTyAtom), RSub)
      );
    _ ->
      union(
        intersect(var(Var), LSub),
        intersect(negate(var(Var)), RSub)
      )
  end.