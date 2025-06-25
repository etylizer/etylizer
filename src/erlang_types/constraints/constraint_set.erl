-module(constraint_set).

-define(TY, ty_node).

meet([], _, _) -> [];
meet(_, [], _) -> [];
meet([[]], Set2, _) -> Set2;
meet(Set1, [[]], _) -> Set1;
meet(S1, S2, Fixed) -> 
  {T0, R} = timer:tc(fun() -> lists:map(fun(E) -> unionlist(S2, E) end, S1) end),
  %io:format(user,"R: ~p~n", [R]),
  {T1, R2} = timer:tc(fun() -> lists:foldl(fun(NewS, All) -> join(NewS, All, Fixed) end, [], R) end),
  %io:format(user,"R2: ~p~n", [R2]),

  case erlang:phash2({S1, S2}) of
    72009357 -> 
      % cprof:start(),
      ok;
    _ -> ok 
  end,

  {T2, Z} = timer:tc(fun() -> minimize(R2) end),

  case erlang:phash2({S1, S2}) of
    72009357 -> 
      % cprof:pause(),
      % ZZ = cprof:analyse(),
      % io:format(user,"~p~n", [ZZ]),
      ok;
    _ -> ok 
  end,

  %io:format(user,"(~p) Phases: ~p  ~p  ~p us~n", [erlang:phash2({S1, S2}), T0, T1, T2]),
  Z.

join([[]], _Set2, _Fixed) -> [[]];
join(_Set1, [[]], _Fixed) -> [[]];
join([], Set, _Fixed) -> Set;
join(Set, [], _Fixed) -> Set;
join(S1, S2, Fixed) ->
  MayAdd = fun (S, Con) -> (not is_empty(Con, Fixed)) andalso (not (has_smaller_constraint(Con, S))) end,
  S22 = lists:filter(fun(C) -> MayAdd(S1, C) end, S2),
  S11 = lists:filter(fun(C) -> MayAdd(S22, C) end, S1),
  lists:map(fun lists:usort/1, lists:usort(S11 ++ S22)).

unionlist(L, A) -> lists:map(fun(E) -> nunion(A, E) end, L).


nunion([], L) -> L;
nunion(L, []) -> L;
nunion(LeftAll = [NextLeft = {V1, T1, T2} | C1], RightAll = [NextRight = {V2, S1, S2} | C2]) ->
  % TODO commit message: variable order was not used here correctly before
  case ty_variable:compare(V1, V2) of
    eq ->
      Lower = ?TY:union(T1, S1),
      Upper = ?TY:intersect(T2, S2),
      [{V1, Lower, Upper}] ++ nunion(C1, C2);
    lt ->
      [NextLeft] ++ nunion(C1, RightAll);
    gt ->
      [NextRight] ++ nunion(C2, LeftAll)
  end.

is_empty(Con, Fixed) -> 
  lists:any(fun({_Var, L, R}) -> 
                case ty_node:normalize(ty_node:difference(L, R), Fixed) of
                  [] ->
                    % io:format(user,"Filtering constraint set: ~p~n", [length(Con)]),
                    true;
                  _ -> false
                end
            end, Con).

 
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
 
has_smaller_constraint(_Con, []) -> false;
has_smaller_constraint(Con, [C | S]) ->
  case is_smaller(C, Con) of
    true -> true;
    _ -> has_smaller_constraint(Con, S)
  end.

% C1 and C2 are sorted by variable order
is_smaller([], _C2) -> true;
is_smaller(_C1, []) -> false;
is_smaller(All = [{V1, T1, T2} | C1], [{V2, S1, S2} | C2]) ->
  case ty_variable:compare(V1, V2) of
    eq ->
      case ty_node:leq(T1, S1) andalso ty_node:leq(S2, T2) of
        true -> is_smaller(C1, C2);
        _ -> false
      end;
    lt ->
      % V1 is not in the other set
      % not smaller
      false;
    gt ->
      is_smaller(All, C2)
  end.








% step 2. from merge phase
% step 1. happens by construction automatically
saturate(C, FixedVariables, Cache) ->
  case pick_bounds_in_c(C, Cache) of
    {_Var, S, T} ->
      SnT = ty_node:intersect(S, ty_node:negate(T)),

      Normed = ty_node:normalize(SnT, FixedVariables),
      NewS = meet([C], Normed, FixedVariables),
      
      lists:foldl(fun(NewC, AllS) ->
        NewMerged = saturate(NewC, FixedVariables, Cache#{SnT => true}),
        join(AllS, NewMerged, FixedVariables)
                  end, [], NewS);
    none -> 
      [C]
  end.

pick_bounds_in_c([], _) -> none;
pick_bounds_in_c([{Var, S, T} | Cs], Memo) ->
  case (ty_node:is_empty(S) orelse ty_node:leq(ty_node:any(), T)) of
    true ->
      pick_bounds_in_c(Cs, Memo);
    false ->
      SnT = ty_node:intersect(S, ty_node:negate(T)),
      case sets:is_element(SnT, Memo) of
        true ->
          pick_bounds_in_c(Cs, Memo);
        _ ->
          {Var, S, T}
      end
  end.









% -ifdef(TEST).
% -include_lib("eunit/include/eunit.hrl").

% smaller_test() ->
%   test_utils:reset_ets(),
%   % {(β≤0)} <: {(β≤0) (β≤α)}
%   Alpha = ty_variable:new(alpha),
%   Beta = ty_variable:new(beta),
%   C1 = [{Beta, ty_rec:empty(), ty_rec:empty()}],
%   C2 = [{Alpha, Beta, ty_rec:any()}, {Beta, ty_rec:empty(), ty_rec:empty()}],

%   true = is_smaller(C1, C2),
%   false = is_smaller(C2, C1),
%   ok.

% smaller2_test() ->
%   test_utils:reset_ets(),
%   % C1 :: {(atom≤β≤1)}
%   % C2 :: {(   1≤β≤1)}
%   Beta = ty_variable:new(beta),
%   Atom = ty_rec:atom(dnf_var_ty_atom:any()), % replacement for bool
%   C1 = [{Beta, Atom,         ty_rec:any()}],
%   C2 = [{Beta, ty_rec:any(), ty_rec:any()}],

%   % C1 =< C2 iff
%   %        (beta, >=, atom) in C1
%   %     => (beta, >=, 1)    in C2 such that 1 >= atom (true)
%   true = is_smaller(C1, C2),
%   ok.

% paper_example_test() ->
%   test_utils:reset_ets(),
%   % C1 :: {(β≤α≤1)    (0≤β≤0)} :: {(β≤α)    (β≤0)}
%   % C2 :: {(β≤α≤1) (atom≤β≤1)} :: {(atom≤β) (β≤α)}
%   % C3 :: {           (0≤β≤0)} :: {(0≤β)         }
%   % C4 :: {(β≤α≤1)    (1≤β≤1)} :: {(1≤β)    (β≤α)}
%   Alpha = ty_variable:new(alpha),
%   Beta = ty_variable:new(beta),
%   BetaTy = ty_rec:variable(Beta),
%   Atom = ty_rec:atom(dnf_var_ty_atom:any()),
%   C1 = [{Alpha, BetaTy, ty_rec:any()}, {Beta, ty_rec:empty(), ty_rec:empty()}],
%   C2 = [{Alpha, BetaTy, ty_rec:any()}, {Beta, Atom, ty_rec:any()}],
%   C3 = [{Beta, ty_rec:empty(), ty_rec:empty()}],
%   C4 = [{Alpha, BetaTy, ty_rec:any()}, {Beta, ty_rec:any(), ty_rec:any()}],

%   true = is_smaller(C2, C4),
%   false = is_smaller(C4, C2),

%   true = is_smaller(C3, C1),
%   false = is_smaller(C1, C3),

%   % proper reduce test, C4 is redundant
%   S = [C2, C4, C1],
%   Min = minimize(S),
%   true = length(Min) =:= 2,

%   ok.


% -endif.
