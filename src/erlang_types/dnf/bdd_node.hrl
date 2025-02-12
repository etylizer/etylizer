% bdd for type kinds (tuples, functions, lists)

-include("bdd.hrl").

substitute({terminal, 1}, _Map, _Memo,_) -> {terminal, 1};
substitute({terminal, 0}, _Map, _Memo,_) -> {terminal, 0};
substitute({terminal, X}, Map, Memo, ApplyToNode) ->
  {terminal, ApplyToNode(X, Map, Memo)};
substitute({node, Node, Left, Right}, StdMap, Memo, ApplyToNode) ->
  T = ApplyToNode(Node, StdMap, Memo),
  T1 = {node, T, any(), empty()},
  union(
    intersect(T1, substitute(Left, StdMap, Memo, ApplyToNode)),
    intersect(negate(T1), substitute(Right, StdMap, Memo, ApplyToNode))
  ).