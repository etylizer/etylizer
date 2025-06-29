-module(etally).

-define(TY, ty_node).

-compile(export_all).

% -export([
%   tally/1,
%   tally/2,
%   is_tally_satisfiable/2
% ]).

% -include("sanity.hrl").

% early return if constraints are found to be satisfiable
% does not solve the equations
is_tally_satisfiable(Constraints, MonomorphicVariables) ->
  % io:format(user,"TALLY~n~s~n", [set_of_constraint_sets:print(Constraints)]),
  % Normalized = ?TIME(tally_normalize, tally_normalize(Constraints, MonomorphicVariables)),
  % io:format(user,"~n=== Step 1: Normalize~n~p~n~p~n===~n~n", [Constraints, MonomorphicVariables]),
  Normalized = tally_normalize(Constraints, MonomorphicVariables),

  % io:format(user,"~n=== Step 2: Saturate~n~p sets of constraint sets~n", [length(Normalized)]),
  % io:format(user,"~p~n", [Normalized]),
  % Saturated = ?TIME(tally_is_satisfiable, tally_saturate_until_satisfiable(Normalized, MonomorphicVariables)),
  Saturated = tally_saturate_until_satisfiable(Normalized, MonomorphicVariables),
  % io:format(user,"SAT~n~p~n", [Saturated]),

  % sanity against full tally calculation
  % ?SANITY(tally_satisfiable_sound, case {tally_saturate(Normalized, MonomorphicVariables), Saturated} of {[], false} -> ok; {[_ | _], true} -> ok end),
   
  Saturated.

% TODO solve
tally(Constraints) -> tally(Constraints, #{}).

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

  % debug for tally 09
  % io:format(user,"Solution~n~p~n", [Solved]),
  % [#{
  %   {var, name, alpha} := N1,
  %   {var, name, beta} := N2,
  %   {var, name, gamma} := N3,
  %   {var, name, delta} := N4
  %  }] = Solved,
  % io:format(user,"Alpha: ~p~n~p~n", [N1, ty_parser:unparse(N1)]),
  % io:format(user,"Beta: ~p~n~p~n", [N2, ty_parser:unparse(N2)]),
  % io:format(user,"Gamma: ~p~n~p~n", [N3, ty_parser:unparse(N3)]),
  % io:format(user,"Delta: ~p~n~p~n", [N4, ty_parser:unparse(N4)]),
  % io:format(user,"~n~n", []),

  % TODO sanity: every substitution satisfies all given constraints, if no error
  % ?SANITY(substitutions_solve_input_constraints, case Solved of {error, _} -> ok; _ -> [ true = is_valid_substitution(Constraints, Subst) || Subst <- Solved] end),
 
  Solved.

tally_normalize(Constraints, MonomorphicVariables) ->
  lists:foldl(fun
    ({_S, _T}, []) -> [];
    ({S, T}, A) -> 
      %io:format(user,"[Tally I] Normalize ~p and ~p:~n~p~nand~n~p~n", [S, T, ty_node:dump(S), ty_node:dump(T)]),
      SnT = ?TY:difference(S, T),
      % io:format(user,"[Tally I] Normalize the difference ~p:~n~p~n", [SnT, ty_node:dump(SnT)]),
      Normalized = ?TY:normalize(SnT, MonomorphicVariables),
      %io:format(user,"Meeting:~n~p~nand~n~p~n", [A, Normalized]),
      {Time, R} = timer:tc(fun() -> constraint_set:meet(A, Normalized, MonomorphicVariables) end),
      %io:format(user,"Result meet:~n~p~n", [R]),
      % io:format(user,"Time: ~p us  Sizes:~p and ~p -> ~p~n", [Time, length(A), length(Normalized), length(R)]),
      R
              end, [[]], Constraints).

tally_saturate_until_satisfiable(Normalized, MonomorphicVariables) ->
  lists:any(fun(ConstraintSet) -> 
                case constraint_set:saturate(ConstraintSet, MonomorphicVariables, _Cache = #{}) of
                  [] -> false;
                  _ -> true
                end
            end, Normalized).

tally_saturate(Normalized, MonomorphicVariables) ->
  lists:foldl(
    fun
      (ConstraintSet, [[]]) -> error(todo_shortcut);
      (ConstraintSet, A) ->
        constraint_set:join(A, constraint_set:saturate(ConstraintSet, MonomorphicVariables, _Cache = #{}), MonomorphicVariables) 
    end, [], Normalized).

tally_solve([], _MonomorphicVariables) -> {error, []};
tally_solve(Saturated, MonomorphicVariables) ->
  Solved = solve(Saturated, MonomorphicVariables),
  [ maps:from_list(Subst) || Subst <- Solved].

solve(SaturatedSetOfConstraintSets, MonomorphicVariables) ->
  S = ([ solve_single(C, [], MonomorphicVariables) || C <- SaturatedSetOfConstraintSets]),
  [ unify(E) || E <- S].

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

