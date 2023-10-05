-module(etally).

-export([
  tally/1,
  tally/2
]).


is_valid_substitution([], _) -> true;
is_valid_substitution([{Left, Right} | Cs], Substitution) ->
  SubstitutedLeft = ty_rec:substitute(Left, Substitution),
  SubstitutedRight = ty_rec:substitute(Right, Substitution),
  ty_rec:is_subtype(SubstitutedLeft, SubstitutedRight) andalso
    is_valid_substitution(Cs, Substitution).


tally(Constraints, FixedVars) ->
  % TODO heuristic here and benchmark
  Normalized = lists:foldl(fun({S, T}, A) ->
    constraint_set:meet(
      fun() -> A end,
      fun() ->
        SnT = ty_rec:diff(S, T),
        ty_rec:normalize(SnT, FixedVars, sets:new())
      end
    )
              end, [[]], Constraints),


  Saturated = lists:foldl(fun(ConstraintSet, A) ->
    constraint_set:join(
      fun() -> A end,
      fun() -> constraint_set:saturate(ConstraintSet, FixedVars, sets:new()) end
    )
                           end, [], Normalized),


  Solved = case Saturated of
    [] -> {error, []};
    _ -> solve(Saturated, FixedVars)
  end,

  case Solved of
        {error, []} ->
          {error, []};
        _ ->
          % TODO expensive sanity check
          % sanity: every substitution satisfies all given constraints
          [true = is_valid_substitution(Constraints, maps:from_list(Subst)) || Subst <- Solved],
          Solved
      end.

%%-spec tally(constraint:simple_constraints()) -> [substitution:t()] | {error, [{error, string()}]}.
tally(Constraints) ->
  tally(Constraints, sets:new()).

solve(SaturatedSetOfConstraintSets, FixedVariables) ->
  S = ([ solve_single(C, [], FixedVariables) || C <- SaturatedSetOfConstraintSets]),
  [unify(E) || E <- S].

solve_single([], Equations, _) -> Equations;
solve_single([{SmallestVar, Left, Right} | Cons], Equations, Fix) ->
  % constraints are already sorted by variable ordering
  % smallest variable first
  FreshTyVar = ty_rec:variable(ty_variable:new("tally_fresh")),
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

  true = length(EquationList) - 1 == length(E_),

  Sigma = unify(E_),
  NewTASigma = apply_substitution(NewTA, Sigma),

  [{Var, NewTASigma}] ++ Sigma.

apply_substitution(Ty, Substitutions) ->
  % io:format(user, "Applying: ~p with ~p~n", [Ty, Substitutions]),
  SubstFun = fun({Var, To}, Tyy) ->
    Mapping = #{Var => To},
    ty_rec:substitute(Tyy, Mapping)
    end,
  lists:foldl(SubstFun, Ty, Substitutions).

% TODO implement & benchmark the minimization
%%minimize_solutions(X = {fail, _}) -> X;
%%minimize_solutions(M) ->
%%  R = lists:filter(fun(Sigma) -> not can_be_removed(Sigma, M) end, M),
%%
%%  case R of
%%    M -> M;
%%    _ ->
%%      % ?LOG_DEBUG("Successfully reduced tally solution size! ~p -> ~p", length(M), length(R)),
%%      R
%%  end.
%%
%%can_be_removed(Sigma, AllSubs) ->
%%  % does Sigma' exist such that
%%  lists:any(fun(SigmaPrime) ->
%%    % dom(Sigma') <: dom(Sigma)
%%    domain(SigmaPrime, Sigma)
%%    andalso
%%    %for all alpha \in dom(sigma'): sigma'(alpha) ~ sigma(alpha)
%%    sub_domain_equivalent(SigmaPrime, Sigma)
%%            end, lists:delete(Sigma, AllSubs)).
%%
%%
%%domain(Sigma1, Sigma2) ->
%%  S1 = [Var || {Var, _} <- Sigma1],
%%  S2 = [Var || {Var, _} <- Sigma2],
%%  gb_sets:is_subset(gb_sets:from_list(S1), gb_sets:from_list(S2)).
%%
%%sub_domain_equivalent(S1, S2) ->
%%  SAll = [Var || {Var, _} <- S1],
%%  lists:all(fun(Var) ->
%%    [Ty] = [T || {V, T} <- S1, V == Var],
%%    [Ty2] = [T || {V, T} <- S2, V == Var],
%%    ty_rec:is_equivalent(Ty, Ty2)
%%            end, SAll).
