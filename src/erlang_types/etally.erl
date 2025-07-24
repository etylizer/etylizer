-module(etally).

-define(TY, ty_node).


-export_type([monomorphic_variables/0]).

-export([
  tally/1,
  tally/2,
  is_tally_satisfiable/2
]).

-type constraint_set() :: constraint_set:constraint_set().
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type monomorphic_variables() :: #{variable() => _}.
-type variable() :: ty_variable:type().
-type input_constraint() :: {ty:type(), ty:type()}.
-type input_constraints() :: [input_constraint()].
-type tally_solutions() :: [#{variable() => ty:type()}].

% -include("sanity.hrl").

% early return if constraints are found to be satisfiable
% does not solve the equations
-spec is_tally_satisfiable(input_constraints(), monomorphic_variables()) -> boolean().
is_tally_satisfiable(Constraints, MonomorphicVariables) ->
  % io:format(user,"TALLY~n~s~n", [set_of_constraint_sets:print(Constraints)]),
  % Normalized = ?TIME(tally_normalize, tally_normalize(Constraints, MonomorphicVariables)),
  io:format(user,"~n=== Step 1: Normalize~n~p~n~p~n===~n~n", [Constraints, MonomorphicVariables]),
  T0 = os:system_time(millisecond),
  Normalized = tally_normalize(Constraints, MonomorphicVariables),
  % io:format(user,"Normalize in ~p ms: ~p~n~p~n", [os:system_time(millisecond)-T0, length(Normalized), Normalized]),
  io:format(user,"Normalize in ~p ms~n", [(T1 = os:system_time(millisecond))-T0]),
  io:format(user,"Result~n~p~n", [Normalized]),
  % [Set] = Normalized,
  % [begin 
  %   io:format(user, "~n~n~p~n", [V]),
  %   % io:format(user, "~p~n", [ty_node:dumpp(L)])
  %   io:format(user, "~p~n", [ty_node:dumpp(R)])
  %  end|| {V, L, R} <- Set],
  % error(todo),

  io:format(user,"~n=== Step 2: Saturate~n~p sets of constraint sets~n", [length(Normalized)]),
  % io:format(user,"~p~n", [Normalized]),
  % Saturated = ?TIME(tally_is_satisfiable, tally_saturate_until_satisfiable(Normalized, MonomorphicVariables)),
  Saturated = tally_saturate_until_satisfiable(Normalized, MonomorphicVariables),
  io:format(user,"Saturate in ~p ms~n", [(os:system_time(millisecond))-T1]),
  % io:format(user,"SAT~n~p~n", [Saturated]),

  % sanity against full tally calculation
  % ?SANITY(tally_satisfiable_sound, case {tally_saturate(Normalized, MonomorphicVariables), Saturated} of {[], false} -> ok; {[_ | _], true} -> ok end),
   
  Saturated.

-spec tally(input_constraints()) -> {error, []} | tally_solutions().
tally(Constraints) -> tally(Constraints, #{}).

-spec tally(input_constraints(), monomorphic_variables()) -> {error, []} | tally_solutions().
tally(Constraints, MonomorphicVariables) ->
  % io:format(user,"TALLY~n~s~n", [set_of_constraint_sets:print(Constraints)]),
  % Normalized = ?TIME(tally_normalize, tally_normalize(Constraints, MonomorphicVariables)),
  % io:format(user,"~n=== Step 1: Normalize~n~p~n===~n~n", [Constraints]),
  Normalized = tally_normalize(Constraints, MonomorphicVariables),

  % io:format(user,"~n=== Step 2: Saturate~n~p sets of constraint sets~n", [length(Normalized)]),
  % io:format(user,"~p~n", [Normalized]),
  Saturated = tally_saturate(Normalized, MonomorphicVariables),
  % Saturated = ?TIME(tally_saturate, tally_saturate(Normalized, MonomorphicVariables)),
 
  % io:format(user,"SAT~n~p~n", [Saturated]),
  % Solved = ?TIME(tally_solve, tally_solve(Saturated, MonomorphicVariables)),
  Solved = tally_solve(Saturated, MonomorphicVariables),

  % TODO sanity: every substitution satisfies all given constraints, if no error
  % ?SANITY(substitutions_solve_input_constraints, case Solved of {error, _} -> ok; _ -> [ true = is_valid_substitution(Constraints, Subst) || Subst <- Solved] end),
 
  Solved.

-spec tally_normalize(input_constraints(), monomorphic_variables()) -> set_of_constraint_sets().
tally_normalize(Constraints, MonomorphicVariables) ->
  lists:foldl(fun
    ({_S, _T}, []) -> [];
    ({S, T}, A) -> 
      %io:format(user,"[Tally I] Normalize ~p and ~p:~n~p~nand~n~p~n", [S, T, ty_node:dump(S), ty_node:dump(T)]),
      SnT = ?TY:difference(S, T),
      % io:format(user,"[Tally I] Normalize the difference ~p:~n~p~n", [SnT, ty_node:dump(SnT)]),
      Normalized = ?TY:normalize(SnT, MonomorphicVariables),
      %io:format(user,"Meeting:~n~p~nand~n~p~n", [A, Normalized]),
      constraint_set:meet(A, Normalized, MonomorphicVariables)
              end, [[]], Constraints).

-spec tally_saturate_until_satisfiable(set_of_constraint_sets(), monomorphic_variables()) -> boolean().
tally_saturate_until_satisfiable(Normalized, MonomorphicVariables) ->
  lists:any(fun(ConstraintSet) -> 
                case constraint_set:saturate(ConstraintSet, MonomorphicVariables, _Cache = #{}) of
                  [] -> false;
                  _ -> true
                end
            end, Normalized).

-spec tally_saturate(set_of_constraint_sets(), monomorphic_variables()) -> set_of_constraint_sets().
tally_saturate(Normalized, MonomorphicVariables) ->
  lists:foldl(
    fun
      (_ConstraintSet, [[]]) -> error(todo_shortcut);
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
  %FreshVar = ty_variable:fresh_from(SmallestVar), 
  FreshTyVar = ty_node:make(dnf_ty_variable:singleton(SmallestVar)),
  % io:format(user,"~p = ~p & (~p U ~p)~n", [SmallestVar, Left, FreshTyVar, Right]),

  Result = ty_node:intersect(ty_node:union(Left, FreshTyVar), Right),
  NewEq = Equations ++ [{eq, SmallestVar, Result}],

  solve_single(Cons, NewEq, Fix).


-spec unify([equation()]) -> [{variable(), ty:type()}].
unify([]) -> [];
unify(EquationList) ->
  % sort to smallest variable
  % select in E the equation α = tα for smallest α
  [Eq = {eq, Var, TA} | _Tail] = lists:usort(fun({_, Var, _}, {_, Var2, _}) -> ty_variable:leq(Var, Var2) end, EquationList),
 
  % io:format(user,"Unify ~p -> ~p~n", [Var, TA]),
  NewMap = #{Var => TA},

  E_ = 
  [ begin
      % io:format(user,"Substitute ~p in ~p = ~p~n", [TA, XA, TAA]),
      {eq, XA, ty_node:substitute(TAA, NewMap)} 
    end
        ||
    (X = {eq, XA, TAA}) <- EquationList, X /= Eq
  ],

  % TODO sanity
  % ?SANITY(solve_equation_list_length, true = length(EquationList) - 1 == length(E_)),

  Sigma = unify(E_),
  % io:format(user,"Σ: ~p~n", [Sigma]),
  NewTASigma = apply_substitution(TA, Sigma),

  [{Var, NewTASigma}] ++ Sigma.


% TODO apply substitution all at once
-spec apply_substitution(ty:type(), [{variable(), ty:type()}]) -> ty:type().
apply_substitution(Ty, []) -> Ty;
apply_substitution(Ty, Substitutions) ->
  % io:format(user, "Applying: ~p with ~p~n", [Ty, Substitutions]),
  SubstFun = fun({Var, To}, Tyy) ->
    Mapping = #{Var => To},
    Result = ty_node:substitute(Tyy, Mapping),
    % TODO sanity
    %?SANITY(etally_apply_substition, sanity_substitution({Var, To}, Tyy, Result)),
    Result
             end,
  lists:foldl(SubstFun, Ty, Substitutions).

