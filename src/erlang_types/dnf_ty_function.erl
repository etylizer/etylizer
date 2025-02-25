-module(dnf_ty_function).

-ifdef(TEST).
-export([explore_function_norm_corec/6]).
-endif.

-define(ELEMENT, ty_function).
-define(TERMINAL, ty_bool).

-define(F(Z), fun() -> Z end).

-export([apply_to_node/3]).
-export([normalize_corec/6, substitute/4, is_empty_corec/2]).

-export([function/1]).

%-type ty_ref() :: {ty_ref, integer()}.
-type dnf_function() :: term().
-type ty_function() :: dnf_function().
-type dnf_ty_function() :: term().

-include("dnf/bdd_node.hrl").

-spec function(ty_function()) -> dnf_ty_function().
function(TyFunction) -> node(TyFunction).

is_empty_corec(TyBDD, M) ->
  dnf(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2}).

is_empty_coclause_corec(AllPos, Neg, T, M) ->
  case {AllPos, Neg, ty_bool:empty()} of
    {_, _, T} -> true;
    {[], [], _} -> false;
    {[], Neg = [TNeg | _], _} ->
      Dim = length(ty_function:domains(TNeg)),
      P = ty_function:function([ty_rec:empty() || _ <- lists:seq(1, Dim)], ty_rec:any()),
      BigSTuple = lists:foldl(fun(FunTy, Acc) ->
        ty_rec:union(Acc, domains_to_tuple(ty_function:domains(FunTy)))
                              end, domains_to_tuple(ty_function:domains(P)), []),
      is_empty_cont_corec(BigSTuple, AllPos, Neg, M);
    {[P | Pos], Neg, _} ->
      % TODO here do these simplifications
      % A -> B && C -> B == A|C -> B
      % A -> B && A -> C == A -> B&C
      BigSTuple = lists:foldl(fun(FunTy, Acc) ->
        ty_rec:union(Acc, domains_to_tuple(ty_function:domains(FunTy)))
                              end, domains_to_tuple(ty_function:domains(P)), Pos),
      is_empty_cont_corec(BigSTuple, AllPos, Neg, M)
  end.

is_empty_cont_corec(_, _, [], _M) -> false;
is_empty_cont_corec(BigSTuple, P, [Function | N], M) ->
  Ts = ty_function:domains(Function),
  T2 = ty_function:codomain(Function),
  (
      %% ∃ Ts-->T2 ∈ N s.t.
      %%    Ts is in the domains of the function
      %%    BigS is the union of all domains of the positive function intersections
      ty_rec:is_empty_corec(ty_rec:intersect(domains_to_tuple(Ts), ty_rec:negate(BigSTuple)), M)
        andalso
        explore_function_corec(domains_to_tuple(Ts), ty_rec:negate(T2), P, M)
  )
  %% Continue searching for another arrow ∈ N
    orelse
    is_empty_cont_corec(BigSTuple, P, N, M).

domains_to_tuple(Domains) ->
  ty_rec:tuple(length(Domains), dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(Domains)))).

% optimized phi' (4.10) from paper covariance and contravariance
% justification for this version of phi can be found in `prop_phi_function.erl`
%-spec explore_function(ty_ref(), ty_ref(), [term()]) -> boolean().
explore_function_corec(Ts, T2, [], M) ->
  ty_rec:is_empty_corec(T2, M) orelse ty_rec:is_empty_corec(Ts, M);
explore_function_corec(Ts, T2, [Function | P], M) ->
  ty_rec:is_empty_corec(Ts, M) orelse ty_rec:is_empty_corec(T2, M)
  orelse
    begin
      BigS1 = domains_to_tuple(ty_function:domains(Function)),
      S2 = ty_function:codomain(Function),
      explore_function_corec(Ts, ty_rec:intersect(T2, S2), P, M)
        andalso
        explore_function_corec(ty_rec:diff(Ts, BigS1), T2, P, M)
    end.

normalize_corec(_Size, DnfTyFunction, [], [], Fixed, M) ->
  dnf(DnfTyFunction, {
    fun(Pos, Neg, DnfTyList) -> normalize_coclause_corec(Pos, Neg, DnfTyList, Fixed, M) end,
    fun constraint_set:meet/2
  })
;
normalize_corec(Size, DnfTyFunction, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:function(Size, dnf_var_ty_function:function(DnfTyFunction)),
  % ntlv rule
  ty_variable:normalize_corec(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:function(Size, dnf_var_ty_function:var(Var)) end, M).

normalize_coclause_corec([], [], T, _Fixed, _M) ->
  case ty_bool:empty() of T -> [[]]; _ -> [] end;
normalize_coclause_corec(Pos, Neg, T, Fixed, M) ->
  case ty_bool:empty() of
    T -> [[]];
    _ ->
      [First | _] = Pos ++ Neg,
      Size = length(ty_function:domains(First)),
      S = lists:foldl(fun ty_rec:union/2, ty_rec:empty(), [domains_to_tuple(Refs) || {ty_function, Refs, _} <- Pos]),
      normalize_no_vars_corec(Size, S, Pos, Neg, Fixed, M)
  end.

normalize_no_vars_corec(_Size, _, _, [], _Fixed, _) -> []; % non-empty
normalize_no_vars_corec(Size, S, P, [Function | N], Fixed, M) ->
  T1 = domains_to_tuple(ty_function:domains(Function)),
  T2 = ty_function:codomain(Function),
  %% ∃ T1-->T2 ∈ N s.t.
  %%   T1 is in the domain of the function
  %%   S is the union of all domains of the positive function intersections
  X1 = ?F(ty_rec:normalize_corec(ty_rec:intersect(T1, ty_rec:negate(S)), Fixed, M)),
  X2 = ?F(explore_function_norm_corec(Size, T1, ty_rec:negate(T2), P, Fixed, M)),
  R1 = ?F(constraint_set:meet(X1, X2)),
  %% Continue searching for another arrow ∈ N
  R2 = ?F(normalize_no_vars_corec(Size, S, P, N, Fixed, M)),
  constraint_set:join(R1, R2).


explore_function_norm_corec(_Size, BigT1, T2, [], Fixed, M) ->
  NT1 = ?F(ty_rec:normalize_corec(BigT1, Fixed, M)),
  NT2 = ?F(ty_rec:normalize_corec(T2, Fixed, M)),
  constraint_set:join( NT1, NT2 );
explore_function_norm_corec(Size, T1, T2, [Function | P], Fixed, M) ->
  NT1 = ?F(ty_rec:normalize_corec(T1, Fixed, M)),
  NT2 = ?F(ty_rec:normalize_corec(T2, Fixed, M)),

  S1 = domains_to_tuple(ty_function:domains(Function)),
  S2 = ty_function:codomain(Function),

  NS1 = ?F(explore_function_norm_corec(Size, T1, ty_rec:intersect(T2, S2), P, Fixed, M)),
  NS2 = ?F(explore_function_norm_corec(Size, ty_rec:diff(T1, S1), T2, P, Fixed, M)),

  constraint_set:join(NT1,
    ?F(constraint_set:join(NT2,
      ?F(constraint_set:meet(NS1, NS2))))).

apply_to_node(Node, Map, Memo) ->
  substitute(Node, Map, Memo, fun(N, S, M) -> ty_function:substitute(N, S, M) end).
