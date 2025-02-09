-ifndef(ELEMENT).
-define(ELEMENT, ty_bool).
-endif.
-ifndef(TERMINAL).
-define(TERMINAL, ty_bool).
-endif.

-export([diff/2, all_variables/1, all_variables/2, transform/2, raw_transform/2, has_ref/2]).

% generic implementations that make use of the shared DNF representation
diff(A, B) -> intersect(A, negate(B)).

all_variables(Ty) -> all_variables(Ty, #{}).
all_variables(Ty, M) ->
  dnf(Ty, {
    fun
      (P,N,T) ->
        ?TERMINAL:all_variables(T, M) ++
          lists:foldl(fun(L, Acc) -> Acc ++ ?ELEMENT:all_variables(L, M) end, [], P) ++
          lists:foldl(fun(L, Acc) -> Acc ++ ?ELEMENT:all_variables(L, M) end, [], N)
    end,
    fun(F1, F2) -> lists:usort(F1() ++ F2()) end
  }).

transform(Ty, Ops = #{negate := Negate, intersect := Intersect, union := Union}) ->
  dnf(Ty, {
    fun
      (P,N,T) ->
        P1 = ?TERMINAL:transform(T, Ops),
        P2 = [?ELEMENT:transform(V, Ops) || V <- P],
        P3 = [Negate(?ELEMENT:transform(V, Ops)) || V <- N],
        Intersect([P1] ++ P2 ++ P3)
    end,
    fun(F1, F2) -> Union([F1(), F2()]) end
  }).

raw_transform(Ty, Ops = #{negate := Negate, intersect := Intersect, union := Union}) ->
  dnf(Ty, {
    fun
      (P,N,T) ->
        P1 = ?TERMINAL:raw_transform(T, Ops),
        P2 = [?ELEMENT:raw_transform(V, Ops) || V <- P],
        P3 = [Negate(?ELEMENT:raw_transform(V, Ops)) || V <- N],
        Intersect([P1] ++ P2 ++ P3)
    end,
    fun(F1, F2) -> Union([F1(), F2()]) end
  }).

has_ref(Ty, Ref) ->
  dnf(Ty, {
    fun
      (P,N,T) ->
        Fun = fun(F) -> ?ELEMENT:has_ref(F, Ref) end,
        ?TERMINAL:has_ref(T, Ref) orelse
          lists:any(Fun, P) orelse
          lists:any(Fun, N)
    end,
    fun(F1, F2) -> F1() orelse F2() end
  }).