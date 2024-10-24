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

normalize(Size, Ty, Fixed, M) -> 
  {Time2, Sol2} = timer:tc(fun() -> 
    dnf(Ty, {
      fun(Pos, Neg, DnfTy) -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
      fun constraint_set:meet/2
    })
  end),
  {Time, Sol} = timer:tc(fun() -> 
    Dnf = simplify(get_full_dnf(Ty)),
    lists:foldl(fun({Pos, Neg, DnfTy}, Acc) -> 
      OtherLazy = fun() -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
      constraint_set:meet(Acc, OtherLazy)
    end, [[]], Dnf)
  end),
  case Time > 1000 orelse Time2 > 1000 of
    true -> io:format(user,"~p vs ~p (~p)~n",[Time, Time2, Time/Time2]);
    _ -> ok
  end,
  Sol.
  

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_function:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_function:substitute(N, Subst, M) end).


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
  DnfFun0 = lists:filter(fun
    ({Pvar, Nvar, Pos, Neg}) -> 
      Ty = ty_rec:of_function_dnf(Arity, Pvar, Nvar, Pos, Neg),
      not ty_rec:is_empty(Ty)
  end, DnfFun),

  % Remove useless summands
  % TODO: Find new test case
  % The above optimization already removes all cases
  DnfFunSum = lists:filter(fun({Pvar, Nvar, Pos, Neg}) ->
    % Dnf without
    D1 = DnfFun0 -- [{Pvar, Nvar, Pos, Neg}],

    TyWithout = ty_rec:of_function_dnfs(Arity, D1),
    TyWith = ty_rec:of_function_dnfs(Arity, DnfFun0),

    case ty_rec:is_subtype(TyWith, TyWithout) of true -> 
      io:format(user, "Summand is useless!~n~s~nis contained in bigger type~n~s~n", [ty_rec:print(TyWith), ty_rec:print(TyWithout)]),
      false;
      _ -> true
    end
  end, DnfFun0),

  % Remove useless literals
  % TODO Negative literals
  DnfFunLit = lists:map(fun({Pvar, Nvar, Pos, Neg}) ->
    NewPos = lists:filter(fun(P) ->
      % Positive literals without P
      Pos1 = Pos -- [P],
      % DNF with new summand
      D1 = (DnfFunSum -- [{Pvar, Nvar, Pos, Neg}]) ++ [{Pvar, Nvar, Pos1, Neg}],

      TyWithout = ty_rec:of_function_dnfs(Arity, D1),
      TyWith = ty_rec:of_function_dnfs(Arity, DnfFunSum),

      case ty_rec:is_subtype(TyWithout, TyWith) of
        true -> 
          io:format(user, "Literal is useless!~n~s~nis contained in bigger type~n~s~n", [ty_rec:print(TyWith), ty_rec:print(TyWithout)]),
          false;
        false -> true
      end
    end, Pos),
    {Pvar, Nvar, NewPos, Neg}
  end, DnfFunSum),

  % TODO Remove
  begin
    PosBefore = lists:foldl(fun({Pvar, NVvar, Pos, Neg}, Sum) -> length(Pos) + Sum end, 0, DnfFunSum),
    PosAfter = lists:foldl(fun({Pvar, NVvar, Pos, Neg}, Sum) -> length(Pos) + Sum end, 0, DnfFunLit),
    case PosBefore > PosAfter of
      true -> io:format(user, "Removed ~p useless literals~n", [PosBefore - PosAfter]);
      _ -> ok
    end
  end,

  % TODO Merge domains and codomains
  %DnfFun1 = lists:map(fun({Pvar, Nvar, Pos, Neg}) -> {Pvar, Nvar, merge_pos_domains(Pos), Neg} end, DnfFun),

  % TODO apply recursively? (not needed for now)

  % TODO Why does back_to_bdd not accept empty lists?
  % This passes all tests
  case DnfFunLit of
    [] -> [];
    D  -> back_to_bdd(D)
  end
  end.

% TODO This is not correct yet, just for testing
merge_pos_domains([P1 | [P2 | Pos]]) ->
  DomainP1 = ty_function:domains_to_tuple(ty_function:domains(P1)),
  DomainP2 = ty_function:domains_to_tuple(ty_function:domains(P2)),
  CoDomainP1 = ty_function:codomain(P1),
  CoDomainP2 = ty_function:codomain(P2),
  NewPos = case ty_rec:is_equivalent(DomainP1, DomainP2) of
    true -> 
      io:format(user, "Function domains are equivalent!~n", []),
      io:format(user, "Domain tuples: ~w~n", [ty_ref:load(DomainP1)]),
      %merge_pos_domains([ty_function:function([DomainP1], ty_rec:intersect(CoDomainP1, CoDomainP2)) | Pos]);
      [ty_function:function([DomainP1], ty_rec:intersect(CoDomainP1, CoDomainP2)) | Pos];
    false -> %PosMerge = merge_pos_domains([P1 | Pos]),
             %merge_pos_domains([P2 | PosMerge])
             [P1 | [P2 | Pos]]
  end,
  case ty_rec:is_equivalent(CoDomainP1, CoDomainP2) of
    true ->
      io:format(user, "Function codomains are equivalent!", []),
      ok;
    false -> ok
  end,
  %[P1 | [P2 | Pos]];
  NewPos;
merge_pos_domains(Pos) -> Pos.

% TODO can be polymorphic, put into bdd_var.hrl
-spec back_to_bdd([
  {[PosVars :: term()], [NegVars :: term()], [Pos :: term()], [Neg :: term()]}
]) -> [{PosVars :: term(), NegVars :: term(), InnerBdd :: term()}].
back_to_bdd([]) -> error(no);
back_to_bdd([{Pv, Nv, P, N}]) -> 
  L3 = [?TERMINAL:node(T) || T <- P],
  L4 = [?TERMINAL:negate(?TERMINAL:node(T)) || T <- N],
  [{Pv, Nv, lists:foldl(fun(E, Acc) -> ?TERMINAL:intersect(E, Acc) end, ?TERMINAL:any(), L3 ++ L4)}];
back_to_bdd([{Pv, Nv, P, N} | Rest]) -> 
  Clause = back_to_bdd([{Pv, Nv, P, N}]),
  Other = back_to_bdd(Rest),
  Clause ++ Other.
