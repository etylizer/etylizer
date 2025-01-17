-module(etally).

-export([
  tally/1,
  tally/2,
  is_tally_satisfiable/2
]).

-include("sanity.hrl").

% early return if constraints are found to be satisfiable
% does not solve the equations
is_tally_satisfiable(Constraints, FixedVars) ->
  % io:format(user,"TALLY~n~s~n", [set_of_constraint_sets:print(Constraints)]),
  Normalized = ?TIME(tally_normalize, tally_normalize(Constraints, FixedVars)),
  % io:format(user,"NORM~n", []),
  Saturated = ?TIME(tally_is_satisfiable, tally_saturate_until_satisfiable(Normalized, FixedVars)),
  % sanity against full tally calculation
  ?SANITY(tally_satisfiable_sound, case {tally_saturate(Normalized, FixedVars), Saturated} of {[], false} -> ok; {[_ | _], true} -> ok end),
  Saturated.

tally(Constraints) -> tally(Constraints, sets:new([{version, 2}])).

tally(Constraints, FixedVars) ->
  % io:format(user,"TALLY~n~s~n", [set_of_constraint_sets:print(Constraints)]),
  Normalized = ?TIME(tally_normalize, tally_normalize(Constraints, FixedVars)),
  % io:format(user,"NORM~n", []),
  Saturated = ?TIME(tally_saturate, tally_saturate(Normalized, FixedVars)),
  % io:format(user,"SAT~n~p~n", [Saturated]),
  Solved = ?TIME(tally_solve, tally_solve(Saturated, FixedVars)),
  % sanity: every substitution satisfies all given constraints, if no error
  ?SANITY(substitutions_solve_input_constraints, case Solved of {error, _} -> ok; _ -> [ true = is_valid_substitution(Constraints, Subst) || Subst <- Solved] end),
  Solved.

tally_normalize(Constraints, FixedVars) ->
  % TODO heuristic here and benchmark
  lists:foldl(fun({S, T}, A) ->
    constraint_set:meet(
      fun() -> A end,
      fun() ->
        SnT = ty_rec:diff(S, T),
        ty_rec:normalize_start(SnT, FixedVars)
      end
    )
              end, [[]], Constraints).

tally_saturate_until_satisfiable(Normalized, FixedVars) ->
  lists:any(fun(ConstraintSet) -> 
    case constraint_set:saturate(ConstraintSet, FixedVars, sets:new()) of
      [] -> false;
      _ -> true
    end
  end, Normalized).

tally_saturate(Normalized, FixedVars) ->
  lists:foldl(fun(ConstraintSet, A) ->
    constraint_set:join(
      fun() -> A end,
      fun() -> constraint_set:saturate(ConstraintSet, FixedVars, sets:new([{version, 2}])) end
    )
              end, [], Normalized).

tally_solve([], _FixedVars) -> {error, []};
tally_solve(Saturated, FixedVars) ->
  Solved = solve(Saturated, FixedVars),
  [ maps:from_list(Subst) || Subst <- Solved].

solve(SaturatedSetOfConstraintSets, FixedVariables) ->
  S = ([ solve_single(C, [], FixedVariables) || C <- SaturatedSetOfConstraintSets]),
  [ unify(E) || E <- S].

solve_single([], Equations, _) -> Equations;
solve_single([{SmallestVar, Left, Right} | Cons], Equations, Fix) ->
  % constraints are already sorted by variable ordering
  % smallest variable first
  % also TODO: why are variable names atoms?
  FreshVar = ty_variable:fresh_from(SmallestVar), 
  FreshTyVar = ty_rec:variable(FreshVar),

  % io:format(user,"[Fresh]~n~p => ~p~n", [SmallestVar, FreshVar]),
  % io:format(user,"[EQ]~n~p = ~p~n", [SmallestVar, lists:usort(lists:flatten(ty_rec:all_variables(Left) ++ ty_rec:all_variables(Right)))]),
  NewEq = Equations ++ [{eq, SmallestVar, ty_rec:intersect(ty_rec:union(Left, FreshTyVar), Right)}],

  solve_single(Cons, NewEq, Fix).

unify([]) -> [];
unify(EquationList) ->
  % sort to smallest variable
  % select in E the equation α = tα for smallest α
  [Eq = {eq, Var, TA} | _Tail] = lists:usort(fun({_, Var, _}, {_, Var2, _}) -> ty_variable:compare(Var, Var2) =< 0 end, EquationList),
  
  Vars = ty_rec:all_variables(TA),
  NewTA = case length([Z || Z <- Vars, Z == Var]) of
            0 ->
              TA;
            _ ->
              % TODO this should work, but not tested yet. Needs a test case
              error({todo, implement_recursive_unification}),
              % create new recursive type μX
              MuX = ty_ref:new_ty_ref(),

              % define type
              % μX.(tα{X/α}) (X fresh)
              Mapping = #{Var => MuX},
              Inner = ty_rec:substitute(TA, Mapping),
              ty_ref:define_ty_ref(MuX, ty_ref:load(Inner)),
              MuX
          end,

  NewMap = #{Var => NewTA},

  E_ = [
    {eq, XA, ty_rec:substitute(TAA, NewMap)} ||
    (X = {eq, XA, TAA}) <- EquationList, X /= Eq
  ],

  ?SANITY(solve_equation_list_length, true = length(EquationList) - 1 == length(E_)),

  Sigma = unify(E_),
  NewTASigma = apply_substitution(NewTA, Sigma),

  [{Var, NewTASigma}] ++ Sigma.

apply_substitution(Ty, Substitutions) ->
  % io:format(user, "Applying: ~p with ~p~n", [Ty, Substitutions]),
  SubstFun = fun({Var, To}, Tyy) ->
    Mapping = #{Var => To},
    Result = ty_rec:substitute(Tyy, Mapping),
    ?SANITY(etally_apply_substition, sanity_substitution({Var, To}, Tyy, Result)),
    Result
             end,
  lists:foldl(SubstFun, Ty, Substitutions).

