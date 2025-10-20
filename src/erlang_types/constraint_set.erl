-module(constraint_set).

-define(LAZY(Term), fun() -> Term end).

-export([
  meet/3,
  join/3,
  saturate/3
]).

-export_type([
  set_of_constraint_sets/0, 
  constraint_set/0
]).

% not opaque: we match on unsatisfiable and satisfiable constraint sets [] and [[]]
-type set_of_constraint_sets() :: [constraint_set()].
-type monomorphic_variables() :: etally:monomorphic_variables().
-type constraint_set() :: [constraint()].
-type constraint() :: {ty_variable:type(), ty:type(), ty:type()}.
-type cache() :: #{ty:type() => []}.


-spec meet(S, S, monomorphic_variables()) -> S when S :: set_of_constraint_sets().
meet([], _, _) -> [];
meet(_, [], _) -> [];
meet([[]], Set2, _) -> Set2;
meet(Set1, [[]], _) -> Set1;
meet(S1, S2, Fixed) -> 
  % when a constraint set is combined, the lower and upper bounds for a variable might change
  % this in turn could mean the whole constraint set can become unsatisfiable
  % it is appararently faster to join everything together, 
  % then minimizing the meet result by using join
  MeetResult = [[join_constraint_sets(C1, C2, Fixed) || C2 <- S2] || C1 <- S1],
  R = lists:foldl(fun(S, Acc) -> join(S, Acc, Fixed) end, [], MeetResult),
  assert_all_cs_sorted(minimize(R)).

% TODO this implementation creates smaller result set of constraint sets, investigate
% meet(S1, S2, Fixed) -> 
%   AllCombinations = [{C1, C2} || C1 <- S1, C2 <- S2],
%   % meet in such a way that bigger constraint sets get filtered out
%   lists:foldl(
%     fun({Cs1, Cs2}, Acc) ->
%       % when a constraint set is combined, the lower and upper bounds for a variable might change
%       % this in turn could mean the whole constraint set can become unsatisfiable
%       % TODO investigate why for user_04 keeping the constraint sets minimal increases time by a lot
%       %      -> change join_constraint_sets to return unsatisfiable again
%       NewCs = join_constraint_sets(Cs1, Cs2, Fixed),
%       case NewCs of
%         unsatisfiable -> Acc;
%         _ ->
%           case lists:any(fun(Cs) -> is_smaller(Cs, NewCs) end, Acc) of
%             true -> 
%               % Acc contains a constraint set that is smaller than NewCs
%               % We can skip adding NewCs to the Acc
%               Acc;
%             false -> 
%               % Remove any existing constraints that NewCs subsumes
%               FilteredAcc = [C || C <- Acc, not is_smaller(NewCs, C)],
%               [NewCs | FilteredAcc]
%           end
%       end
%     end,
%     [],
%     AllCombinations
%   ).

-spec join(S, S, monomorphic_variables()) -> S when S :: set_of_constraint_sets().
join([[]], _Set2, _Fixed) -> [[]];
join(_Set1, [[]], _Fixed) -> [[]];
join([], Set, _Fixed) -> Set;
join(Set, [], _Fixed) -> Set;
join(S1, S2, Fixed) ->
  MayAdd = fun (S, Con) -> (not is_unsatisfiable(Con, Fixed)) andalso (not (has_smaller_constraint(Con, S))) end,
  S22 = lists:filter(fun(C) -> MayAdd(S1, C) end, S2),
  S11 = lists:filter(fun(C) -> MayAdd(S22, C) end, S1),
  assert_all_cs_sorted((lists:usort(S11 ++ S22))).

% step 2. from merge phase
% step 1. happens by construction automatically
-spec saturate(constraint_set(), monomorphic_variables(), cache()) -> set_of_constraint_sets().
saturate(C, FixedVariables, Cache) ->
  case pick_bounds_in_c(C, Cache) of
    {_Var, S, T} ->
      SnT = ty:difference(S, T),
      Normed = ty:normalize(SnT, FixedVariables),
      NewS = meet([C], Normed, FixedVariables),
      Z = lists:foldl(fun(NewC, AllS) ->
        NewMerged = saturate(NewC, FixedVariables, Cache#{SnT => []}),
        join(AllS, NewMerged, FixedVariables)
                  end, [], NewS),
      Z;
    none -> 
      [C]
  end.

% helper functions
-spec join_constraint_sets(Cs, Cs, monomorphic_variables()) -> unsatisfiable | Cs when Cs :: constraint_set().
join_constraint_sets([], L, _) -> L;
join_constraint_sets(L, [], _) -> L;
join_constraint_sets(LeftAll = [NextLeft = {V1, T1, T2} | C1], RightAll = [NextRight = {V2, S1, S2} | C2], Fixed) ->
  ReturnIfUnsat = fun (_Cs, unsatisfiable) -> unsatisfiable; (Cs, Other) -> Cs ++ Other end,
  case ty_variable:compare(V1, V2) of
    eq ->
      Lower = ty:union(T1, S1),
      Upper = ty:intersect(T2, S2),
      ReturnIfUnsat([{V1, Lower, Upper}], join_constraint_sets(C1, C2, Fixed));
      % TODO user_04 is much slower because a lot of ty:normalize checks are used, investigate
      % if the new lower bound is not subtype of the new upper bound, 
      % the whole constraint set is unsatisfiable
      % we can't use a subtype check here, as we need to consider polymorphic variables properly
      % case ty:normalize(ty:difference(Lower, Upper), Fixed) of
      %   [] -> unsatisfiable;
      %   _ -> ReturnIfUnsat([{V1, Lower, Upper}], join_constraint_sets(C1, C2, Fixed))
      % end;
    lt ->
      ReturnIfUnsat([NextLeft], join_constraint_sets(C1, RightAll, Fixed));
    gt ->
      ReturnIfUnsat([NextRight], join_constraint_sets(C2, LeftAll, Fixed))
  end.

-spec is_unsatisfiable
  (constraint(), monomorphic_variables()) -> boolean();
  (constraint_set(), monomorphic_variables()) -> boolean().
is_unsatisfiable({_Var, L, R}, Fixed) -> 
  case ty_node:normalize(ty_node:difference(L, R), Fixed) of 
    [] -> true; 
    _ -> false 
  end;
is_unsatisfiable(Con, Fixed) -> 
  lists:any(fun(C) -> is_unsatisfiable(C, Fixed) end, Con).

-spec has_smaller_constraint(constraint_set(), set_of_constraint_sets()) -> boolean().
has_smaller_constraint(_Con, []) -> false;
has_smaller_constraint(Con, [C | S]) ->
  case is_smaller(C, Con) of
    true -> true;
    _ -> has_smaller_constraint(Con, S)
  end.

% C1 and C2 are sorted by variable order
-spec is_smaller(constraint_set(), constraint_set()) -> boolean().
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

-spec pick_bounds_in_c(constraint_set(), cache()) -> none | constraint().
pick_bounds_in_c([], _) -> none;
pick_bounds_in_c([{Var, S, T} | Cs], Memo) ->
  case (ty_node:is_empty(S) orelse ty_node:leq(ty_node:any(), T)) of
    true ->
      pick_bounds_in_c(Cs, Memo);
    false ->
      SnT = ty_node:intersect(S, ty_node:negate(T)),
      case Memo of
        #{SnT := []} ->
          pick_bounds_in_c(Cs, Memo);
        _ ->
          {Var, S, T}
      end
  end.

-spec minimize(S) -> S when S :: set_of_constraint_sets().
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

assert_all_cs_sorted(S) ->
    % Verify all constraint sets are sorted by sorting them and checking for equality
    lists:foreach(fun(ConstraintSet) ->
        Sorted = lists:sort(
            fun({Var1, _, _}, {Var2, _, _}) ->
                case ty_variable:compare(Var1, Var2) of
                    lt -> true;
                    eq -> true;
                    gt -> false
                end
            end,
            ConstraintSet
        ),
        case ConstraintSet =:= Sorted of
            true -> ok;
            false -> error({unsorted_constraint_set, ConstraintSet, Sorted})
        end
    end, S),
    S.

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

% TODO why does Dialyzer complain that L. 256 has no return?
-dialyzer({no_return, [smaller_test/0]}).
-spec smaller_test() -> _.
smaller_test() ->
  global_state:with_new_state(fun() ->
    % {(β≤0)} <: {(β≤0) (β≤α)}
    Alpha = ty_variable:new_with_name(alpha),
    Beta = ty_variable:new_with_name(beta),
    C1 = [{Beta, ty:empty(), ty:empty()}],
    % β < α according to variable order and constraint sets are ordered
    C2 = [{Beta, ty:empty(), ty:empty()}, {Alpha, Beta, ty:any()}],

    true = is_smaller(C1, C2),
    false = is_smaller(C2, C1)
  end).

-spec smaller2_test() -> _.
smaller2_test() ->
  global_state:with_new_state(fun() ->
    % C1 :: {(atom≤β≤1)}
    % C2 :: {(   1≤β≤1)}
    Beta = ty_variable:new_with_name(beta),
    Atom = ty:atom(), % replacement for bool
    C1 = [{Beta, Atom,     ty:any()}],
    C2 = [{Beta, ty:any(), ty:any()}],

    % C1 =< C2 iff
    %        (beta, >=, atom) in C1
    %     => (beta, >=, 1)    in C2 such that 1 >= atom (true)
    true = is_smaller(C1, C2)
  end).

-spec paper_example_test() -> _.
paper_example_test() ->
  global_state:with_new_state(fun() ->
    % C1 :: {(β≤α≤1)    (0≤β≤0)} :: {(β≤α)    (β≤0)}
    % C2 :: {(β≤α≤1) (atom≤β≤1)} :: {(atom≤β) (β≤α)}
    % C3 :: {           (0≤β≤0)} :: {(0≤β)         }
    % C4 :: {(β≤α≤1)    (1≤β≤1)} :: {(1≤β)    (β≤α)}
    Alpha = ty_variable:new_with_name(alpha),
    Beta = ty_variable:new_with_name(beta),
    BetaTy = ty:variable(Beta),
    Atom = ty:atom(),
    C1 = [{Beta, ty:empty(), ty:empty()}, {Alpha, BetaTy, ty:any()} ],
    C2 = [{Beta, Atom, ty:any()}, {Alpha, BetaTy, ty:any()}],
    C3 = [{Beta, ty:empty(), ty:empty()}],
    C4 = [{Beta, ty:any(), ty:any()}, {Alpha, BetaTy, ty:any()}],

    true = is_smaller(C2, C4),
    false = is_smaller(C4, C2),

    true = is_smaller(C3, C1),
    false = is_smaller(C1, C3),

    % proper reduce test, C4 is redundant
    S = [C2, C4, C1],
    Min = minimize(S),
    true = length(Min) =:= 2
  end).

-endif.
