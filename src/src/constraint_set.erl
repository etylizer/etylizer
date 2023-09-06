-module(constraint_set).
-vsn({2,0,0}).

%% API
-export([set_of_constraint_sets/1, constraint_set/1, constraint/3, constraint/1, is_smaller/2]).
-export([merge_and_meet/2, merge_and_join/2, has_smaller_constraint_w/2, has_smaller_constraint/2]).
-export([meet/2, join/2, minimize/1]).
-export([saturate/3]).

% step 2. from merge phase
% step 1. happens by construction automatically
saturate(C, FixedVariables, Memo) ->
  case pick_bounds_in_c(C, Memo) of
    {_Var, S, T} ->
      SnT = ty_rec:intersect(S, ty_rec:negate(T)),
      Normed = fun() -> ty_rec:normalize(SnT, FixedVariables, sets:new()) end,
      NewS = meet(fun() -> [C] end, Normed),
      lists:foldl(fun(NewC, AllS) ->
        NewMerged = fun() -> saturate(NewC, FixedVariables, sets:union(Memo, sets:from_list([SnT]))) end,
        join(fun() -> AllS end, NewMerged)
                  end, [], NewS);
    _ -> [C]
  end.

pick_bounds_in_c([], _) -> none;
pick_bounds_in_c([{Var, S, T} | Cs], Memo) ->
  case (ty_rec:is_empty(S) orelse ty_rec:is_subtype(ty_rec:any(), T)) of
    true -> pick_bounds_in_c(Cs, Memo);
    false ->
      SnT = ty_rec:intersect(S, ty_rec:negate(T)),
      case sets:is_element(SnT, Memo) of
        true -> pick_bounds_in_c(Cs, Memo);
        _ -> {Var, S, T}
      end
  end
.

set_of_constraint_sets(S) -> S.
constraint_set(Cs) when is_list(Cs) -> Cs.
constraint(Var, Ty1, Ty2) -> {Var, Ty1, Ty2}.
constraint({Var, Ty1, Ty2}) -> {Var, Ty1, Ty2}.

meet(S1, S2) ->
  Res = S1(),
  case Res of
    [] -> [];
    _ -> merge_and_meet(Res, S2())
  end.
join(S1, S2) ->
  Res = S1(),
  case Res of
    [[]] -> [[]];
    _ -> merge_and_join(Res, S2())
  end.

merge_and_meet([], _Set2) -> [];
merge_and_meet(_Set1, []) -> [];
merge_and_meet([[]], Set2) -> Set2;
merge_and_meet(Set1, [[]]) -> Set1;
merge_and_meet(La, Lb) ->
  R = lists:map(fun(E) -> unionlist(Lb, E) end, La),
  R2 = lists:foldl(fun(NewS, All) -> merge_and_join(NewS, All) end, [], R),
  minimize(R2).

unionlist(L, A) -> lists:map(fun(E) -> nunion(A, E) end, L).

minimize(S) -> minimize(S, S).

minimize([], Result) -> Result;
minimize([Cs | Others], All) ->
  NewS = All -- [Cs],
  case has_smaller_constraint(Cs, NewS) of
    true ->
      true = length(NewS) < length(All),
      minimize(NewS, NewS);
    _ -> minimize(Others, All)
  end.


nunion([], L) -> L;
nunion(L, []) -> L;
nunion([{V1, T1, T2} | C1], [{V2, S1, S2} | C2]) when V1 == V2 ->
  Lower = ty_rec:union(T1, S1),
  Upper = ty_rec:intersect(T2, S2),

  [{V1, Lower, Upper}] ++ nunion(C1, C2);
nunion([Z = {V1, _, _} | C1], S = [{V2, _, _} | _C2]) when V1 < V2 ->
  [Z] ++ nunion(C1, S);
nunion(S = [{_, _, _} | _C1], [Z = {_, _, _} | C2]) ->
  [Z] ++ nunion(C2, S).


merge_and_join([[]], _Set2) -> [[]];
merge_and_join(_Set1, [[]]) -> [[]];
merge_and_join([], Set) -> Set;
merge_and_join(Set, []) -> Set;
merge_and_join(S1, S2) ->
  MayAdd = fun (S, Con) -> (not (has_smaller_constraint(Con, S))) end,
  S22 = lists:filter(fun(C) -> MayAdd(S1, C) end, S2),
  S11 = lists:filter(fun(C) -> MayAdd(S22, C) end, S1),
  lists:map(fun lists:usort/1, lists:usort(S11 ++ S22)).


has_smaller_constraint(_Con, []) -> false;
has_smaller_constraint(Con, [C | S]) ->
  case is_smaller(C, Con) of
    true -> true;
    _ -> has_smaller_constraint(Con, S)
  end.

has_smaller_constraint_w(_Con, []) -> false;
has_smaller_constraint_w(Con, [C | S]) ->
  case is_smaller(C, Con) of
    true -> {true, C};
    _ -> has_smaller_constraint(Con, S)
  end.

% C1 and C2 are sorted by variable order
is_smaller([], _C2) -> true;
is_smaller(_C1, []) -> false;
is_smaller([{V1, T1, T2} | C1], [{V2, S1, S2} | C2]) when V1 == V2 ->
  case ty_rec:is_subtype(T1, S1) andalso ty_rec:is_subtype(S2, T2) of
    true -> is_smaller(C1, C2);
    _ -> false
  end;
is_smaller([{V1, _, _} | _C1], [{V2, _, _} | _C2]) when V1 < V2 ->
  % V1 is not in the other set
  % not smaller
  false;
is_smaller(C1, [{_V2, _, _} | C2]) ->
  is_smaller(C1, C2).


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

smaller_test() ->
  % {(β≤0)} <: {(β≤0) (β≤α)}
  Alpha = ty_variable:new("alpha"),
  Beta = ty_variable:new("beta"),
  C1 = [{Beta, ty_rec:empty(), ty_rec:empty()}],
  C2 = [{Alpha, Beta, ty_rec:any()}, {Beta, ty_rec:empty(), ty_rec:empty()}],

  true = is_smaller(C1, C2),
  false = is_smaller(C2, C1),
  ok.

smaller2_test() ->
  % C1 :: {(atom≤β≤1)}
  % C2 :: {(   1≤β≤1)}
  Beta = ty_variable:new("beta"),
  Atom = ty_rec:atom(dnf_var_ty_atom:any()), % replacement for bool
  C1 = [{Beta, Atom,         ty_rec:any()}],
  C2 = [{Beta, ty_rec:any(), ty_rec:any()}],

  % C1 =< C2 iff
  %        (beta, >=, atom) in C1
  %     => (beta, >=, 1)    in C2 such that 1 >= atom (true)
  true = is_smaller(C1, C2),
  ok.

paper_example_test() ->
  % C1 :: {(β≤α≤1)    (0≤β≤0)} :: {(β≤α)    (β≤0)}
  % C2 :: {(β≤α≤1) (atom≤β≤1)} :: {(atom≤β) (β≤α)}
  % C3 :: {           (0≤β≤0)} :: {(0≤β)         }
  % C4 :: {(β≤α≤1)    (1≤β≤1)} :: {(1≤β)    (β≤α)}
  Alpha = ty_variable:new("alpha"),
  Beta = ty_variable:new("beta"),
  BetaTy = ty_rec:variable(Beta),
  Atom = ty_rec:atom(dnf_var_ty_atom:any()),
  C1 = [{Alpha, BetaTy, ty_rec:any()}, {Beta, ty_rec:empty(), ty_rec:empty()}],
  C2 = [{Alpha, BetaTy, ty_rec:any()}, {Beta, Atom, ty_rec:any()}],
  C3 = [{Beta, ty_rec:empty(), ty_rec:empty()}],
  C4 = [{Alpha, BetaTy, ty_rec:any()}, {Beta, ty_rec:any(), ty_rec:any()}],

  true = is_smaller(C2, C4),
  false = is_smaller(C4, C2),

  true = is_smaller(C3, C1),
  false = is_smaller(C1, C3),

  % proper reduce test, C4 is redundant
  S = [C2, C4, C1],
  Min = minimize(S),
  true = length(Min) =:= 2,

  ok.


-endif.
