-module(etally).

-export([
  tally/1,
  tally/2
]).

-define(debug, true).

-include_lib("../log.hrl").
-include_lib("sanity.hrl").

tally(Constraints) -> tally(Constraints, sets:new()).

tally(Constraints, FixedVars) ->
  Normalized = ?TIME(tally_normalize, tally_normalize(Constraints, FixedVars)),
  Saturated = ?TIME(tally_saturate, tally_saturate(Normalized, FixedVars)),
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
        ty_rec:normalize(SnT, FixedVars, sets:new())
      end
    )
              end, [[]], Constraints).

tally_saturate(Normalized, FixedVars) ->
  lists:foldl(fun(ConstraintSet, A) ->
    constraint_set:join(
      fun() -> A end,
      fun() -> constraint_set:saturate(ConstraintSet, FixedVars, sets:new()) end
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
  % FIXME: HACK
  % also TODO: why are variable names atoms?
  FreshVar = ast_lib:ast_to_erlang_ty_var(stdtypes:tvar(list_to_atom("tally_" ++ integer_to_list(ty_variable:get_new_id())))),
  %ty_rec:variable(ty_variable:new("tally_fresh")),
  FreshTyVar = ty_rec:variable(FreshVar),
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
    sanity_substitution({Var, To}, Tyy, Result),
    Result
             end,
  lists:foldl(SubstFun, Ty, Substitutions).

sanity_substitution({Var, _To}, Ty, TyAfter) ->
  case lists:member(Var, ty_rec:all_variables(Ty)) of
    false ->  ok;
    true ->
      case lists:member(Var, ty_rec:all_variables(TyAfter)) of
        false -> ok;
        _ ->
          error({failed_sanity, Var, variable_is_still_in_ty_after_substitution, {before, ty_rec:print(Ty)}, {'after', ty_rec:print(TyAfter)}})
      end
  end.


% sanity check
is_valid_substitution([], _) -> true;
is_valid_substitution([{Left, Right} | Cs], Substitution) ->
  SubstitutedLeft = ty_rec:substitute(Left, Substitution),
  SubstitutedRight = ty_rec:substitute(Right, Substitution),
  Res = ty_rec:is_subtype(SubstitutedLeft, SubstitutedRight) ,
  case Res of
    false ->
      io:format(user, "Left: ~s -> ~s~n", [ty_rec:print(Left), ty_rec:print(SubstitutedLeft)]),
      io:format(user, "Right: ~s -> ~s~n", [ty_rec:print(Right), ty_rec:print(SubstitutedRight)]);
    _ -> ok
  end,
  Res andalso
    is_valid_substitution(Cs, Substitution).
