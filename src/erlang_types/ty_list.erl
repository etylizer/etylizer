-module(ty_list).

-export([compare/2, equal/2]).
-export([list/2, pi1/1, pi2/1, has_ref/2, transform/2, big_intersect/1, substitute/3, all_variables/1]).

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

list(Ref1, Ref2) -> {ty_list, Ref1, Ref2}.

pi1({ty_list, Ref, _}) -> Ref.
pi2({ty_list, _, Ref}) -> Ref.

has_ref({ty_list, Ref, _}, Ref) -> true;
has_ref({ty_list, _, Ref}, Ref) -> true;
has_ref({ty_list, _, _}, _Ref) -> false.

transform({ty_list, A, B}, #{to_list := ToList}) ->
  ToList(A, B).

big_intersect(All) ->
  lists:foldl(fun({ty_list, S, T}, {ty_list, A, B}) ->
    {ty_list, ty_rec:intersect(S, A), ty_rec:intersect(T, B)}
              end, {ty_list, ty_rec:any(), ty_rec:any()}, All).

substitute({ty_list, A, B}, Map, Memo) ->
  {ty_list,
    ty_rec:substitute(A, Map, Memo),
    ty_rec:substitute(B, Map, Memo)
  }.

all_variables({ty_list, A, B}) ->
  ty_rec:all_variables(A) ++
  ty_rec:all_variables(B).
