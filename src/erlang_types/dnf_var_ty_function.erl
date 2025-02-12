-module(dnf_var_ty_function).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_function).
-define(F(Z), fun() -> Z end).


-export([is_empty_corec/2]).
-export([normalize_corec/4, substitute/4]).
-export([var/1, function/1]).

-include("dnf/bdd_var.hrl").

function(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

is_empty_corec(TyBDD, M) -> dnf(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2}).
is_empty_coclause_corec(_Pos, _Neg, T, M) -> dnf_ty_function:is_empty_corec(T, M).

normalize_corec(Size, Ty, Fixed, M) -> 
  % Simplifies DNF
  Dnf = simplify(get_full_dnf(Ty)),
  lists:foldl(fun({Pos, Neg, DnfTy}, Acc) ->
    % Normalization also merges function types, simplifying the type
    OtherLazy = fun() -> dnf_ty_function:normalize_corec(Size, DnfTy, Pos, Neg, Fixed, M) end,
    constraint_set:meet(Acc, OtherLazy)
  end, [[]], Dnf).

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_function:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_function:substitute(N, Subst, M) end).


% Simplifies a given DNF by removing summands equivalent to empty, useless summands and useless literals
simplify([]) -> [];
simplify(DnfFun) ->
  NonVars = lists:flatten([P ++ N || {_, _, P, N} <- DnfFun, length(P ++ N) > 0]),
  % function constructor needs arity, and arity is implicit in the function BDD
  % for BDDs with only variables and no function part, we skip the simplification step
  case NonVars of
    [] -> back_to_bdd(DnfFun); % only contains variable parts
    [F | _] ->

  % otherwise, we can extract the arity from any clause
  Arity = length(ty_function:domains(F)),

  % Remove 0 summands
  DnfFun0 = lists:filter(fun({Pvar, Nvar, Pos, Neg}) ->
      Ty = ty_rec:of_function_dnf(Arity, Pvar, Nvar, Pos, Neg),
      not ty_rec:is_empty(Ty)
  end, DnfFun),

  % Remove useless summands
  % TODO: Find new test case
  % The above optimization already removes all cases
  DnfFunSum = lists:filter(fun(Sum) ->
    % Dnf without
    D1 = DnfFun0 -- [Sum],

    TyWithout = ty_rec:of_function_dnfs(Arity, D1),
    TyWith = ty_rec:of_function_dnfs(Arity, DnfFun0),

    not ty_rec:is_subtype(TyWith, TyWithout)
  end, DnfFun0),

  % Remove useless literals
  DnfFunLit = lists:map(fun({Pvar, Nvar, Pos, Neg}) ->
    Filter = fun(Literal, B) ->

      % DNF with new summand
      D1 = case B of
        pos -> S1 = Pos -- [Literal],
               (DnfFunSum -- [{Pvar, Nvar, Pos, Neg}]) ++ [{Pvar, Nvar, S1, Neg}];
        neg -> S1 = Neg -- [Literal],
               (DnfFunSum -- [{Pvar, Nvar, Pos, Neg}]) ++ [{Pvar, Nvar, Pos, S1}]
      end,

      TyWithout = ty_rec:of_function_dnfs(Arity, D1),
      TyWith = ty_rec:of_function_dnfs(Arity, DnfFunSum),

      % Check if the new type is a subtype of the original one
      not ty_rec:is_subtype(TyWithout, TyWith)
    end,
    
    NewPos = lists:filter(fun(P) -> Filter(P, pos) end, Pos),
    NewNeg = lists:filter(fun(N) -> Filter(N, neg) end, Neg),

    {Pvar, Nvar, NewPos, NewNeg}
  end, DnfFunSum),

  % Merge domains and codomains => This is done in dnf_ty_function

  % TODO apply recursively? (not needed for now)

  back_to_bdd(DnfFunLit)
  end.

% TODO can be polymorphic, put into bdd_var.hrl
-spec back_to_bdd([
  {[PosVars :: term()], [NegVars :: term()], [Pos :: term()], [Neg :: term()]}
]) -> [{PosVars :: term(), NegVars :: term(), InnerBdd :: term()}].
back_to_bdd([]) -> [];
back_to_bdd([{Pv, Nv, P, N}]) -> 
  L3 = [?TERMINAL:node(T) || T <- P],
  L4 = [?TERMINAL:negate(?TERMINAL:node(T)) || T <- N],
  [{Pv, Nv, lists:foldl(fun(E, Acc) -> ?TERMINAL:intersect(E, Acc) end, ?TERMINAL:any(), L3 ++ L4)}];
back_to_bdd([{Pv, Nv, P, N} | Rest]) -> 
  Clause = back_to_bdd([{Pv, Nv, P, N}]),
  Other = back_to_bdd(Rest),
  Clause ++ Other.
