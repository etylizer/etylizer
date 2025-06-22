-module(ty_list).

compare(A, B) -> ty_tuple:compare(A, B).
equal(P1, P2) -> ty_tuple:equal(P1, P2).
tuple(Refs) -> ty_tuple:tuple(Refs).
empty(Size) -> ty_tuple:empty(Size).
any(Size) -> ty_tuple:any(Size).
components(T) -> ty_tuple:components(T).
pi(I, T) -> ty_tuple:pi(I, T).
big_intersect(X) -> ty_tuple:big_intersect(X).

unparse({ty_tuple, 2, [List, Termination]}, Cache) ->
  {improper_list, ty_node:unparse(List, Cache), ty_node:unparse(Termination, Cache)}.

