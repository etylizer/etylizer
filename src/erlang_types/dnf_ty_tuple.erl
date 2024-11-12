-module(dnf_ty_tuple).

-define(ELEMENT, ty_tuple).
-define(TERMINAL, bdd_bool).
-define(F(Z), fun() -> Z end).

-export([simplify_dnf/1, is_empty_corec/2, normalize_corec/6, substitute/4, apply_to_node/3]).
-export([tuple/1, all_variables/2, transform/2, to_singletons/1, phi_corec/3, phi_norm_corec/5]).

-include("bdd_node.hrl").

tuple(TyTuple) -> node(TyTuple).

to_singletons(TyBDD) ->
  dnf(TyBDD, {fun to_singletons_coclause/3, fun(F1, F2) -> F1() ++ F2() end}).

to_singletons_coclause(Pos, Neg, T) ->
  case {Pos, Neg, bdd_bool:any()} of
    {_, _, T} ->
      % delete the same singletons occurring both as Pos and Neg
      % does not check whether tuples itself singleton
      TyTuples = lists:foldr(fun lists:delete/2, Pos, Neg),
      lists:map(fun(TyTuple) ->
        Ty = dnf_var_ty_tuple:tuple(tuple(TyTuple)),
        ty_rec:tuple({default, []}, Ty)
                end, TyTuples);
    _ ->
      []
  end.


is_empty_corec(TyBDD, M = #{mode := opt}) ->
  dnf(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2});
is_empty_corec(TyBDD, M) ->
  dnf_raw(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2}).

is_empty_coclause_corec(Pos, Neg, T, M) ->
  case {Pos, Neg, bdd_bool:empty()} of
    {_, _, T} -> true;
    {[], [], _} -> false;
    {[], [TNeg | _], _} ->
      Dim = length(ty_tuple:components(TNeg)),
      PosAny = ty_tuple:any(Dim),
      BigS = ty_tuple:big_intersect([PosAny]),
      phi_corec(ty_tuple:components(BigS), Neg, M);
    {Pos, Neg, _} ->
      BigS = ty_tuple:big_intersect(Pos),
      phi_corec(ty_tuple:components(BigS), Neg, M)
  end.

phi_corec(BigS, [], M) ->
  lists:foldl(fun(S, Res) -> Res orelse ty_rec:is_empty_corec(S, M) end, false, BigS);
phi_corec(BigS, [Ty | N], M) ->
  Solve = fun({Index, {_PComponent, NComponent}}, Result) ->
    Result
      andalso
      begin
      % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
        DoDiff = fun({IIndex, PComp}) ->
          case IIndex of
            Index -> ty_rec:diff(PComp, NComponent);
            _ -> PComp
          end
                 end,
        NewBigS = lists:map(DoDiff, lists:zip(lists:seq(1, length(BigS)), BigS)),
        phi_corec(NewBigS, N, M)
      end
          end,


  lists:foldl(fun(S, Res) -> Res orelse ty_rec:is_empty_corec(S, M) end, false, BigS)
    orelse
      lists:foldl(Solve, true, lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty)))).

normalize_corec(Size, Ty, [], [], Fixed, M) ->
  dnf(Ty, {
    fun
      ([], [], T) ->
        case bdd_bool:empty() of T -> [[]]; _ -> [] end;
      ([], Neg = [TNeg | _], T) ->
        case bdd_bool:empty() of
          T -> [[]];
          _ ->
            Dim = length(ty_tuple:components(TNeg)),
            PosAny = ty_tuple:any(Dim),
            BigS = ty_tuple:big_intersect([PosAny]),
            phi_norm_corec(Size, ty_tuple:components(BigS), Neg, Fixed, M)
        end;
      (Pos, Neg, T) ->
        case bdd_bool:empty() of
          T -> [[]];
          _ ->
            BigS = ty_tuple:big_intersect(Pos),
            phi_norm_corec(Size, ty_tuple:components(BigS), Neg, Fixed, M)
        end
    end,
    fun constraint_set:meet/2
  });
normalize_corec(Size, DnfTy, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:tuple(Size, dnf_var_ty_tuple:tuple(DnfTy)),
  % ntlv rule
  ty_variable:normalize_corec(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:tuple(Size, dnf_var_ty_tuple:var(Var)) end, M).

phi_norm_corec(_Size, BigS, [], Fixed, M) ->
  lists:foldl(fun(S, Res) -> constraint_set:join(?F(Res), ?F(ty_rec:normalize_corec(S, Fixed, M))) end, [], BigS);
phi_norm_corec(Size, BigS, [Ty | N], Fixed, M) ->
  Solve = fun({Index, {_PComponent, NComponent}}, Result) ->
    constraint_set:meet(
      ?F(Result),
      ?F(begin
      % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
        DoDiff = fun({IIndex, PComp}) ->
          case IIndex of
            Index ->
              ty_rec:diff(PComp, NComponent);
            _ -> PComp
          end
                 end,
        NewBigS = lists:map(DoDiff, lists:zip(lists:seq(1, length(BigS)), BigS)),
        phi_norm_corec(Size, NewBigS, N, Fixed, M)
      end)
    )
          end,

  constraint_set:join(
    ?F(lists:foldl(fun(S, Res) -> constraint_set:join(?F(Res), ?F(ty_rec:normalize_corec(S, Fixed, M))) end, [], BigS)),
    ?F(lists:foldl(Solve, [[]], lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty)))))
  ).


apply_to_node(Node, Map, Memo) ->
  substitute(Node, Map, Memo, fun(N, S, M) -> ty_tuple:substitute(N, S, M) end).

simplify_dnf([]) -> [];
simplify_dnf(Dnf) ->

  case lists:member({[], [], ?TERMINAL:any()}, Dnf) of
    true -> [{[], [], ?TERMINAL:any()}];
    _ ->
      % step 1: intersect positive 
      A = [{big_intersect(P), N, T} || {P, N, T} <- Dnf],

      % io:format(user, "Left: ~p~n", [A]),
      % step 2: remove negations
      NoNeg = lists:flatten([
        remove_negations(P, N, T, [])
        || {P, N, T} <- A
        ]),

      Res = [{[T], [], ?TERMINAL:any()} || T <- NoNeg],
      % io:format(user, "Remm: ~p~n", [Res]),
      Res
  end.

% assumes P is a single tuple
remove_negations(P, [], _T, Acc) ->
  [P | Acc];
remove_negations([], [NegTuple | N], T, Acc) ->
  remove_negations([ty_tuple:any(length(ty_tuple:components(NegTuple)))], [NegTuple | N], T, Acc);
remove_negations(PP, [NegTuple | N], _T, Acc) ->
  [P] = PP,
  Sis = ty_tuple:components(P),
  Tis = ty_tuple:components(NegTuple),
  Size = length(Sis),

  Dis = [ 
      [case Index of 
          I -> ty_rec:diff(lists:nth(Index, Sis), lists:nth(Index, Tis)); 
          _ -> lists:nth(Index, Sis) 
        end || Index <- lists:seq(1, Size)]
      || I <- lists:seq(1, Size)],



  lists:foldl(fun(Index, AccInner) -> 
    % check if ith component of Di is empty
    % if empty, then skip and continue
    % if not empty, remove_negations on that
    % if all ith Dis are empty, Acc should be returned
    DiTuple = lists:nth(Index, Dis),
    Di = lists:nth(Index, DiTuple),
    % remove_negations([ty_tuple:tuple(DiTuple)], N, _T, AccInner)
    case ty_rec:is_empty_raw(Di) of
      true -> 
        % skip
        AccInner;
      false -> 
        % don't skip
        remove_negations([ty_tuple:tuple(DiTuple)], N, _T, AccInner)
    end
  end, Acc, lists:seq(1, Size)).


big_intersect([]) -> [];
big_intersect([X]) -> [X];
big_intersect(X) -> 
  % io:format(user,"x",[]),
  [ty_tuple:big_intersect(X)].



-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

empty_0tuple_test() ->
  Tuple = {node,{ty_tuple,0,[]},{terminal,0},{terminal,1}},
  true = is_empty_corec(Tuple, #{}),
  ok.

-endif.
