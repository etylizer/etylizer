% bdd for type kinds (tuples, functions, lists)

-include("bdd.hrl").

substitute(_BddRef = {bdd_ref, 0}, _Map, _Memo, _Apply) -> empty();
substitute(BddRef = {bdd_ref, _}, Map, Memo, Apply) -> 
  #{BddRef := Bdd} = get_memory(),
  substitute(Bdd, Map, Memo, Apply);
substitute({terminal, 1}, _Map, _Memo, _ApplyToNode) -> 
  any();
substitute({terminal, X}, Map, Memo, ApplyToNode) ->
  mk_terminal(ApplyToNode(X, Map, Memo));
substitute({node, Node, Left, Right}, StdMap, Memo, ApplyToNode) ->
  T = ApplyToNode(Node, StdMap, Memo),
  T1 = mk_node(T, any(), empty()),
  union(
    intersect(T1, substitute(Left, StdMap, Memo, ApplyToNode)),
    intersect(negate(T1), substitute(Right, StdMap, Memo, ApplyToNode))
  ).