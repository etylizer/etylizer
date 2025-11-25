-module(etally).

-define(TY, ty_node).


-export_type([monomorphic_variables/0]).

-export([
  tally/1,
  tally/2,
  is_tally_satisfiable/2,
  tally_saturate/2,
  is_satisfiable_v2/2
]).

-include("sanity.hrl").

-define(TALLY_DEFAULT(), is_satisfiable_v4).

-type constraint_set() :: constraint_set:constraint_set().
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type normalized_set_of_constraint_sets() :: set_of_constraint_sets(). % normalized set of constraint sets
-type solutions() :: set_of_constraint_sets(). % saturated set of constraint sets
-type monomorphic_variables() :: #{variable() => _}.
-type variable() :: ty_variable:type().
-type input_constraint() :: {ty:type(), ty:type()}.
-type input_constraints() :: [input_constraint()].
-type tally_solutions() :: [#{variable() => ty:type()}].


% early return if constraints are found to be satisfiable
% does not solve the equations
-spec is_tally_satisfiable(input_constraints(), monomorphic_variables()) -> boolean().
is_tally_satisfiable(Constraints, MonomorphicVariables) ->
  case os:getenv(string:to_upper("TALLY")) of
    "v1" -> is_satisfiable_v1(Constraints, MonomorphicVariables);
    "v2" -> is_satisfiable_v2(Constraints, MonomorphicVariables);
    "v3" -> is_satisfiable_v3(Constraints, MonomorphicVariables);
    "v4" -> is_satisfiable_v4(Constraints, MonomorphicVariables);
    _ -> ?TALLY_DEFAULT()(Constraints, MonomorphicVariables)
  end.



% CDuce version without the solve phase, almost paper version
% normalize & first part of merge at the same time,
% then saturation of upper and lower bounds at the end
-spec is_satisfiable_v1(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v1(Constraints, MonomorphicVariables) ->
  % io:format(user,"~n~n=== Step 1: Normalize ~p constraints~n~s~nFixed variables: ~p~n===~n", [length(Constraints), print(Constraints), MonomorphicVariables]),
  Normalized = ?TIME(tally_sat_normalize, tally_normalize(Constraints, MonomorphicVariables)),
  % io:format(user,"~n=== Step 2: Saturate~n~p sets of constraint sets~n", [length(Normalized)]),
  Saturated = ?TIME(tally_sat_saturate, tally_saturate_until_satisfiable(Normalized, MonomorphicVariables)),
  % sanity against full tally calculation
  ?SANITY(tally_satisfiable_sound, case {tally_saturate(Normalized, MonomorphicVariables), Saturated} of {[], false} -> ok; {[_ | _], true} -> ok end),
  Saturated.

-spec tally_saturate_until_satisfiable(normalized_set_of_constraint_sets(), monomorphic_variables()) -> boolean().
tally_saturate_until_satisfiable(Normalized, MonomorphicVariables) ->
  lists:any(
    fun(ConstraintSet) -> 
      case constraint_set:saturate(ConstraintSet, MonomorphicVariables, _Cache = #{}) of 
        [] -> false; 
        _ -> true 
      end 
    end, Normalized).

% slice constraints and merge result, no order
-spec is_satisfiable_v2(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v2(Constraints, MonomorphicVariables) ->
  Z = [tally_saturate(tally_normalize([C], MonomorphicVariables), MonomorphicVariables) || C <- Constraints],
  case lists:all(fun([[]]) -> true; (_) -> false end, Z) of
    true -> true;
    _ ->
      [S | Ss] = Z,
      Z2 = lists:foldl(fun(E, E2) -> tally_saturate(constraint_set:meet(E, E2, MonomorphicVariables), MonomorphicVariables) end, S, Ss),
      case Z2 of
        [] -> false;
        _ -> true
      end
  end.

% slice constraints and merge single solutions first, then multiple solutions last
-spec is_satisfiable_v3(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v3(Constraints, MonomorphicVariables) ->
  Z = [tally_saturate(tally_normalize([C], MonomorphicVariables), MonomorphicVariables) || C <- Constraints],
  case lists:all(fun([[]]) -> true; (_) -> false end, Z) of
    true -> true;
    _ ->
      All0 = Z,
      NotSat = [X || X <- All0, X == []],
      case length(NotSat) > 0 of
        true -> false;
        _ ->
          All = [X || X <- All0, X /= [[]]], 
          All1 = [X || X <- All, length(X) == 1],

          SimpleSat = lists:foldl(fun(E, E2) -> tally_saturate(constraint_set:meet(E, E2, MonomorphicVariables), MonomorphicVariables) end, [[]], All1),
          case SimpleSat of
            [] -> false;
            _ -> 
              All2 = [X || X <- All, length(X) > 1],
              case length(All2) of
                0 -> true;
                _ ->
                  % io:format("Got ~p complex~n", [length(All2)]),
                  % io:format("~n~p~n", [All2]),
                  {T2, ComplexSat} = 
                  timer:tc(fun() -> lists:foldl(fun(E, E2) -> 
                                                    % io:format(user,".~p", [length(E2)]), 
                                                    tally_saturate(constraint_set:meet(E, E2, MonomorphicVariables), MonomorphicVariables) end, SimpleSat, All2) end),
                  % io:format("Complex in ~p ms~n", [T2]),

                  case ComplexSat of
                    [] -> false;
                    _ -> true
                  end
              end
          end
      end
  end.

-spec is_satisfiable_v4(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable_v4(Constraints, MonomorphicVariables) ->  
  % First, normalize and saturate each constraint individually
  InputSolutions = [tally_saturate(tally_normalize([C], MonomorphicVariables), MonomorphicVariables) || C <- Constraints], % [solutions()] :: %
  
  case lists:all(fun([[]]) -> true; (_) -> false end, InputSolutions) of
    true -> true;
    false ->
      Red = [N || N <- InputSolutions, N /= [[]]],
      % then process each set of solutions individually
      process_input_solutions(Red, [[]], MonomorphicVariables)
  end.

-spec process_input_solutions(ToBeProcessed::[solutions()], CurrentResult::solutions(), monomorphic_variables()) -> boolean().
process_input_solutions([], _FinalResult, _MonoVars) -> 
  % No input solutions left to process, finished
  % FinalResult can't be []
  true;
process_input_solutions(TodoSols, CurrentResult, MonoVars) ->
  % T0 = erlang:system_time(millisecond),
  {SelectedSolution, NewResult} = find_least_increasing_solutions(TodoSols, CurrentResult, MonoVars),
  % io:format(user,"~p >> ~p sols (~p ms) (~p todos)~n~s~n", 
  %           [length(CurrentResult), length(NewResult), (erlang:system_time(millisecond)-T0), length(TodoSols), print(SelectedSolution)]
  %          ),
  case NewResult of
    [] -> false;
    _ -> process_input_solutions(TodoSols -- [SelectedSolution], NewResult, MonoVars)
  end.

%% Find the solution that increases solution count the least after saturation
-spec find_least_increasing_solutions(ToBeProcessed::[solutions()], CurrentResult::solutions(), monomorphic_variables()) -> {solutions(), solutions()}.
find_least_increasing_solutions([Sol | Rest], Acc, MonoVars) ->
  MeetResult = constraint_set:meet(Sol, Acc, MonoVars),
  FirstSaturatedResult = tally_saturate(MeetResult, MonoVars),
  case {length(Acc), length(FirstSaturatedResult)} of
    {1, 1} -> {Sol, FirstSaturatedResult}; % special case
    _ ->
      % io:format(user,"Better than ~p -> ~p?~n", [length(Acc), length(FirstSaturatedResult)]),
      find_least_increasing_solutions(Rest, Acc, MonoVars, {Sol, FirstSaturatedResult})
  end.

-spec find_least_increasing_solutions(ToBeProcessed::[solutions()], CurrentResult::solutions(), monomorphic_variables(), {solutions(), solutions()}) -> {solutions(), solutions()}.
find_least_increasing_solutions(All, Acc, MonoVars, Current) ->
  case lists:foldl(fun
    (_, Z = {shortcut, _}) -> Z;
    (S, {Cr, CurrentResult}) -> 
      MeetResult = constraint_set:meet(S, Acc, MonoVars),
      SaturatedResult = tally_saturate(MeetResult, MonoVars),
      if
        length(SaturatedResult) < length(CurrentResult) -> 
          % io:format(user, "Found decreasing solution ~p (~p -> ~p)~n", [erlang:phash2(S), length(CurrentResult), length(SaturatedResult)]),
          {shortcut, {S, SaturatedResult}}; % This is the better solution (decrease sol count)
       length(CurrentResult) < 3 andalso length(SaturatedResult) == length(CurrentResult) -> 
          % io:format(user, "Found good solution ~p (~p)~n", [erlang:phash2(S), length(CurrentResult)]),
          {shortcut, {S, SaturatedResult}}; % This is a good solution (no increase and keeps sol count small)
        true -> {Cr, CurrentResult}
      end
                   end, Current, All) 
  of
    {shortcut, Z} -> Z;
    Z -> Z
  end.

% =========================
% full tally implementation

-spec tally(input_constraints()) -> {error, []} | tally_solutions().
tally(Constraints) -> tally(Constraints, #{}).

-spec tally(input_constraints(), monomorphic_variables()) -> {error, []} | tally_solutions().
tally(Constraints, MonomorphicVariables) ->
  % io:format(user,"~n~n=== Step 1: Normalize ~p constraints~n~s~nFixed variables: ~p~n===~n", [length(Constraints), print(Constraints), MonomorphicVariables]),
  Normalized = ?TIME(tally_normalize, tally_normalize(Constraints, MonomorphicVariables)),
  % io:format(user,"~n~n=== Step 2: Saturate ~p sets~n~s~nFixed variables: ~p~n===~n", [length(Constraints), print(Normalized), MonomorphicVariables]),
  Saturated = ?TIME(tally_saturate, tally_saturate(Normalized, MonomorphicVariables)),
  % io:format(user,"~n~n=== Step 3: Solve ~p sets~n~s~nFixed variables: ~p~n===~n", [length(Constraints), print(Saturated), MonomorphicVariables]),
  Solved = ?TIME(tally_solve, tally_solve(Saturated, MonomorphicVariables)),
  % io:format(user,"~n~n=== Step 4: Solved~n~p~n===~n", [Solved]),

  % sanity: every substitution satisfies all given constraints (by polymorphic subtyping), if no error
  ?SANITY(substitutions_solve_input_constraints, case Solved of {error, _} -> ok; _ -> [ true = is_valid_substitution(Constraints, Subst, MonomorphicVariables) || Subst <- Solved] end),
 
  Solved.

-spec tally_normalize(input_constraints(), monomorphic_variables()) -> set_of_constraint_sets().
tally_normalize(Constraints, MonomorphicVariables) ->
  lists:foldl(fun
    ({_S, _T}, []) -> [];
    ({S, T}, A) -> 
      SnT = ?TY:difference(S, T),
      Normalized = ty_node:normalize(SnT, MonomorphicVariables),
      constraint_set:meet(A, Normalized, MonomorphicVariables)
              end, [[]], Constraints).


-spec tally_saturate(set_of_constraint_sets(), monomorphic_variables()) -> set_of_constraint_sets().
tally_saturate(Normalized, MonomorphicVariables) ->
  lists:foldl(
    fun
      (_ConstraintSet, [[]]) -> [[]];
      (ConstraintSet, A) ->
        constraint_set:join(A, constraint_set:saturate(ConstraintSet, MonomorphicVariables, _Cache = #{}), MonomorphicVariables) 
    end, [], Normalized).

-spec tally_solve(set_of_constraint_sets(), monomorphic_variables()) -> {error, []} | tally_solutions().
tally_solve([], _MonomorphicVariables) -> {error, []};
tally_solve(Saturated, MonomorphicVariables) ->
  Solved = solve(Saturated, MonomorphicVariables),
  [ maps:from_list(Subst) || Subst <- Solved].

-spec solve(set_of_constraint_sets(), monomorphic_variables()) -> [[{variable(), ty:type()}]].
solve(SaturatedSetOfConstraintSets, MonomorphicVariables) ->
  S = ([ solve_single(C, [], MonomorphicVariables) || C <- SaturatedSetOfConstraintSets]),
  [ unify(E) || E <- S].

-type equation() :: {eq, variable(), ty:type()}.
-spec solve_single(constraint_set(), [equation()], monomorphic_variables()) -> [equation()].
solve_single([], Equations, _) -> Equations;
solve_single([{SmallestVar, Left, Right} | Cons], Equations, Fix) ->
  % constraints are already sorted by variable ordering
  % smallest variable first
  % reuse variable
  % FreshTyVar = ty_node:make(dnf_ty_variable:singleton(ty_variable:fresh_from(SmallestVar))), 
  FreshTyVar = ty_node:make(dnf_ty_variable:singleton(SmallestVar)),

  Result = ty_node:intersect(ty_node:union(Left, FreshTyVar), Right),
  NewEq = Equations ++ [{eq, SmallestVar, Result}],

  solve_single(Cons, NewEq, Fix).

-spec unify([equation()]) -> [{variable(), ty:type()}].
unify([]) -> [];
unify(EquationList) ->
  % sort to smallest variable
  % select in E the equation α = tα for smallest α
  [Eq = {eq, Var, TA} | _Tail] = lists:usort(fun({_, Var, _}, {_, Var2, _}) -> ty_variable:leq(Var, Var2) end, EquationList),
 
  NewMap = #{Var => TA},

  E_ = 
  [ begin
      {eq, XA, ty_node:substitute(TAA, NewMap)} 
    end
        ||
    (X = {eq, XA, TAA}) <- EquationList, X /= Eq
  ],

  ?SANITY(solve_equation_list_length, true = length(EquationList) - 1 == length(E_)),

  Sigma = unify(E_),
  NewTASigma = apply_substitution(TA, Sigma),

  [{Var, NewTASigma}] ++ Sigma.


% TODO apply substitution all at once
-spec apply_substitution(ty:type(), [{variable(), ty:type()}]) -> ty:type().
apply_substitution(Ty, []) -> Ty;
apply_substitution(Ty, Substitutions) ->
  SubstFun = fun({Var, To}, Tyy) ->
    Mapping = #{Var => To},
    Result = ty_node:substitute(Tyy, Mapping),
    % since we reuse the tally variables, the same variable can appear again in the result substitution
    % only if we generate fresh variables, include this sanity check
    % ?SANITY(etally_apply_substition, sanity_substitution({Var, To}, Tyy, Result)),
    Result
             end,
  lists:foldl(SubstFun, Ty, Substitutions).

% print([]) -> "";
% print([X | Xs]) when is_list(X) -> 
%   io_lib:format(">>~n~s~n~s", [print(X), print(Xs)]);
% print([{{var, name, Name}, Left, Right} | Rest]) -> 
%   io_lib:format("~s <: ~p <: ~s~n~s", [pretty:render_ty(ty_parser:unparse(Left)), Name, pretty:render_ty(ty_parser:unparse(Right)), print(Rest)]);
% print([{Left, Right} | Rest]) -> 
%   io_lib:format("~s <: ~s~n~s", [pretty:render_ty(ty_parser:unparse(Left)), pretty:render_ty(ty_parser:unparse(Right)), print(Rest)]).
