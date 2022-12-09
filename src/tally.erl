-module(tally).

-include_lib("log.hrl").

-export([
  tally/2,
  tally/3
]).

-spec tally(symtab:t(), constr:simp_constrs(), sets:set(ast:ty_varname())) -> [subst:t()] | {error, [{error, string()}]}.
tally(Symtab, Constraints, FixedVars) ->
  N = tally_norm:norm_api(Constraints, FixedVars, Symtab),
  M = case N of [] -> {fail, norm}; _ -> N end,

  S = tally_solve:solve(M, FixedVars, Symtab),

  Min = minimize_solutions(S, Symtab),
  X = case Min of
    {fail, _X} ->
      {error, []};
    _ ->
      % transform to subst:t()
      [maps:from_list([{VarName, Ty} || {{var, VarName}, Ty} <- Subst]) || Subst <- S]
  end,

  X.

-spec tally(symtab:t(), constr:simp_constrs()) -> [subst:t()] | {error, [{error, string()}]}.
tally(Symtab, Constraints) ->
  tally(Symtab, Constraints, sets:new()).


minimize_solutions(X = {fail, _}, _) -> X;
minimize_solutions(M, Sym) ->
  R = lists:filter(fun(Sigma) -> not can_be_removed(Sigma, M, Sym) end, M),

  case R of
    M -> M;
    _ ->
      ?LOG_DEBUG("Successfully reduced tally solution size! ~p -> ~p", length(M), length(R)),
      R
  end.

can_be_removed(Sigma, AllSubs, Sym) ->
  % does Sigma' exist such that
  lists:any(fun(SigmaPrime) ->
    % dom(Sigma') <: dom(Sigma)
    domain(SigmaPrime, Sigma)
    andalso
    %for all alpha \in dom(sigma'): sigma'(alpha) ~ sigma(alpha)
    sub_domain_equivalent(SigmaPrime, Sigma, Sym)
            end, lists:delete(Sigma, AllSubs)).


domain(Sigma1, Sigma2) ->
  S1 = [Var || {Var, _} <- Sigma1],
  S2 = [Var || {Var, _} <- Sigma2],
  gb_sets:is_subset(gb_sets:from_list(S1), gb_sets:from_list(S2)).

sub_domain_equivalent(S1, S2, Sym) ->
  SAll = [Var || {Var, _} <- S1],
  lists:all(fun(Var) ->
    [Ty] = [T || {V, T} <- S1, V == Var],
    [Ty2] = [T || {V, T} <- S2, V == Var],
    subty:is_equivalent(Sym, Ty, Ty2)
            end, SAll).
