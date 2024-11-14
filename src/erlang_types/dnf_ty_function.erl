-module(dnf_ty_function).

-ifdef(TEST).
-export([explore_function_norm/6]).
-endif.

-define(ELEMENT, ty_function).
-define(TERMINAL, bdd_bool).

-define(F(Z), fun() -> Z end).

-export([apply_to_node/3]).
-export([normalize/6, substitute/4, is_empty/1]).

-export([function/1, all_variables/2, transform/2]).

-type ty_ref() :: {ty_ref, integer()}.
-type dnf_function() :: term().
-type ty_function() :: dnf_function().
-type dnf_ty_function() :: term().

-include("bdd_node.hrl").

-spec function(ty_function()) -> dnf_ty_function().
function(TyFunction) -> node(TyFunction).

is_empty(TyBDD) ->
  dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

is_empty_coclause(AllPos, Neg, T) ->
  case {AllPos, Neg, bdd_bool:empty()} of
    {_, _, T} -> true;
    {[], [], _} -> false;
    {[], Neg = [TNeg | _], _} ->
      Dim = length(ty_function:domains(TNeg)),
      P = ty_function:function([ty_rec:empty() || _ <- lists:seq(1, Dim)], ty_rec:any()),
      BigSTuple = lists:foldl(fun(FunTy, Acc) ->
        ty_rec:union(Acc, domains_to_tuple(ty_function:domains(FunTy)))
                              end, domains_to_tuple(ty_function:domains(P)), []),
      is_empty_cont(BigSTuple, AllPos, Neg);
    {Pos, Neg, _} ->
      % Transform list of function types to tuples
      NewPos = [{domains_to_tuple(ty_function:domains(P)), ty_function:codomain(P)} || P <- Pos],

      % As an optimization merge positive function types
      [{Domains1, _} | Pos1] = merge_pos(NewPos),

      BigSTuple = lists:foldl(fun({Domains, _}, Acc) -> ty_rec:union(Acc, Domains) end, Domains1, Pos1),
      is_empty_cont(BigSTuple, AllPos, Neg)
  end.

% Assume list contains tuples (domain_tuple, codomain)
% Merges positive function types according to following simplification rules:
% (A -> B) ∧ (A -> C) = (A -> B ∧ C)
% (A -> C) ∧ (B -> C) = (A ∨ B -> C)
merge_pos([]) -> [];
merge_pos([P | Rest]) ->
  NewPos = merge_pos_fun(P, Rest),
  % TODO: Find a better way to check that a merge happened
  MergedPos = case Rest == NewPos of
    % Nothing changed, continue with the next function
    true -> [P | merge_pos(Rest)];
    % List changed, i.e. merge happened. Don't need P
    _ ->
      %io:format(user, "Functions merged!~n", []),
      merge_pos(NewPos)
  end,
  MergedPos.

% Merges a single function type with a list of function types
merge_pos_fun(_, []) -> [];
merge_pos_fun({Domains1, Codomain1}, Pos) ->
  % For now just check if the list has the same length
  lists:map(fun({Domains2, Codomain2}) ->
    case {ty_rec:is_equivalent(Domains1, Domains2), ty_rec:is_equivalent(Codomain1, Codomain2)} of
      % They are the same function
      {true, true} -> {Domains1, Codomain1};
      % Domains are equal
      {true, _} -> {Domains1, ty_rec:intersect(Codomain1, Codomain2)};
      % Codomains are equal
      {_, true} -> {ty_rec:union(Domains1, Domains2), Codomain1};
      % No equivalence
      _ -> {Domains2, Codomain2}
      end
  end, Pos).

is_empty_cont(_, _, []) -> false;
is_empty_cont(BigSTuple, P, [Function | N]) ->
  Ts = ty_function:domains(Function),
  T2 = ty_function:codomain(Function),
  (
      %% ∃ Ts-->T2 ∈ N s.t.
      %%    Ts is in the domains of the function
      %%    BigS is the union of all domains of the positive function intersections
      ty_rec:is_subtype(domains_to_tuple(Ts), BigSTuple)
        andalso
        explore_function(domains_to_tuple(Ts), ty_rec:negate(T2), P)
  )
  %% Continue searching for another arrow ∈ N
    orelse
    is_empty_cont(BigSTuple, P, N).

domains_to_tuple(Domains) ->
  ty_rec:tuple(length(Domains), dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(Domains)))).

% optimized phi' (4.10) from paper covariance and contravariance
% justification for this version of phi can be found in `prop_phi_function.erl`
-spec explore_function(ty_ref(), ty_ref(), [term()]) -> boolean().
explore_function(Ts, T2, []) ->
  ty_rec:is_empty(T2) orelse ty_rec:is_empty(Ts);
explore_function(Ts, T2, [Function | P]) ->
  ty_rec:is_empty(Ts) orelse ty_rec:is_empty(T2)
  orelse
    begin
      BigS1 = domains_to_tuple(ty_function:domains(Function)),
      S2 = ty_function:codomain(Function),
      explore_function(Ts, ty_rec:intersect(T2, S2), P)
        andalso
        explore_function(ty_rec:diff(Ts, BigS1), T2, P)
    end.

normalize(_Size, DnfTyFunction, [], [], Fixed, M) ->
  dnf(DnfTyFunction, {
    fun(Pos, Neg, DnfTyList) -> normalize_coclause(Pos, Neg, DnfTyList, Fixed, M) end,
    fun constraint_set:meet/2
  })
;
normalize(Size, DnfTyFunction, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:function(Size, dnf_var_ty_function:function(DnfTyFunction)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:function(Size, dnf_var_ty_function:var(Var)) end, M).

normalize_coclause([], [], T, _Fixed, _M) ->
  case bdd_bool:empty() of T -> [[]]; _ -> [] end;
normalize_coclause(Pos, Neg, T, Fixed, M) ->
  case bdd_bool:empty() of
    T -> [[]];
    _ ->
      [First | _] = Pos ++ Neg,
      Size = length(ty_function:domains(First)),
     
      % TODO: Same optimization as in is_empty_coclause; try to combine them

      % Transform list of function types to tuples
      NewPos = [{domains_to_tuple(ty_function:domains(P)), ty_function:codomain(P)} || P <- Pos],
      % As an optimization merge positive function types
      [{Domains1, _} | Pos1] = merge_pos(NewPos),

      S = lists:foldl(fun({Domains, _}, Acc) -> ty_rec:union(Acc, Domains) end, Domains1, Pos1),

      normalize_no_vars(Size, S, Pos, Neg, Fixed, M)
  end.

normalize_no_vars(_Size, _, _, [], _Fixed, _) -> []; % non-empty
normalize_no_vars(Size, S, P, [Function | N], Fixed, M) ->
  T1 = domains_to_tuple(ty_function:domains(Function)),
  T2 = ty_function:codomain(Function),
  %% ∃ T1-->T2 ∈ N s.t.
  %%   T1 is in the domain of the function
  %%   S is the union of all domains of the positive function intersections
  X1 = ?F(ty_rec:normalize(ty_rec:intersect(T1, ty_rec:negate(S)), Fixed, M)),
  X2 = ?F(explore_function_norm(Size, T1, ty_rec:negate(T2), P, Fixed, M)),
  R1 = ?F(constraint_set:meet(X1, X2)),
  %% Continue searching for another arrow ∈ N
  R2 = ?F(normalize_no_vars(Size, S, P, N, Fixed, M)),
  constraint_set:join(R1, R2).


explore_function_norm(_Size, BigT1, T2, [], Fixed, M) ->
  NT1 = ?F(ty_rec:normalize(BigT1, Fixed, M)),
  NT2 = ?F(ty_rec:normalize(T2, Fixed, M)),
  constraint_set:join( NT1, NT2 );
explore_function_norm(Size, T1, T2, [Function | P], Fixed, M) ->
  NT1 = ?F(ty_rec:normalize(T1, Fixed, M)),
  NT2 = ?F(ty_rec:normalize(T2, Fixed, M)),

  S1 = domains_to_tuple(ty_function:domains(Function)),
  S2 = ty_function:codomain(Function),

  NS1 = ?F(explore_function_norm(Size, T1, ty_rec:intersect(T2, S2), P, Fixed, M)),
  NS2 = ?F(explore_function_norm(Size, ty_rec:diff(T1, S1), T2, P, Fixed, M)),

  constraint_set:join(NT1,
    ?F(constraint_set:join(NT2,
      ?F(constraint_set:meet(NS1, NS2))))).

apply_to_node(Node, Map, Memo) ->
  substitute(Node, Map, Memo, fun(N, S, M) -> ty_function:substitute(N, S, M) end).
