-module(dnf_ty_tuple).

-define(ELEMENT, ty_tuple).
-define(TERMINAL, bdd_bool).
-define(F(Z), fun() -> Z end).

-export([is_empty/1, normalize/6, substitute/4, apply_to_node/3]).
-export([tuple/1, all_variables/1, transform/2]).

-include("bdd_node.hrl").

tuple(TyTuple) -> node(TyTuple).

is_empty(TyBDD) ->
  dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

is_empty_coclause(Pos, Neg, T) ->
  case {Pos, Neg, bdd_bool:empty()} of
    {_, _, T} -> true;
    {[], [], _} -> false;
    {[], [TNeg | _], _} ->
      Dim = length(ty_tuple:components(TNeg)),
      PosAny = ty_tuple:any(Dim),
      BigS = ty_tuple:big_intersect([PosAny]),
      phi(ty_tuple:components(BigS), Neg);
    {Pos, Neg, _} ->
      BigS = ty_tuple:big_intersect(Pos),
      phi(ty_tuple:components(BigS), Neg)
  end.

phi(BigS, []) ->
  lists:foldl(fun(S, Res) -> Res orelse ty_rec:is_empty(S) end, false, BigS);
phi(BigS, [Ty | N]) ->
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
        phi(NewBigS, N)
      end
          end,


  lists:foldl(fun(S, Res) -> Res orelse ty_rec:is_empty(S) end, false, BigS)
    orelse
      lists:foldl(Solve, true, lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty)))).

normalize(Size, Ty, [], [], Fixed, M) ->
  dnf(Ty, {
    fun(Pos, Neg, T) ->
      case bdd_bool:empty() of
        T -> [[]];
        _ ->
          BigS = ty_tuple:big_intersect(Pos),
          phi_norm(Size, ty_tuple:components(BigS), Neg, Fixed, M)
      end
    end,
    fun constraint_set:meet/2
  });
normalize(Size, DnfTy, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:tuple(Size, dnf_var_ty_tuple:tuple(DnfTy)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:tuple(Size, dnf_var_ty_tuple:var(Var)) end, M).

phi_norm(_Size, BigS, [], Fixed, M) ->
  lists:foldl(fun(S, Res) -> constraint_set:join(?F(Res), ?F(ty_rec:normalize(S, Fixed, M))) end, [], BigS);
phi_norm(Size, BigS, [Ty | N], Fixed, M) ->
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
        phi_norm(Size, NewBigS, N, Fixed, M)
      end)
    )
          end,

  constraint_set:join(
    ?F(lists:foldl(fun(S, Res) -> constraint_set:join(?F(Res), ?F(ty_rec:normalize(S, Fixed, M))) end, [], BigS)),
    ?F(lists:foldl(Solve, [[]], lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty)))))
  ).


apply_to_node(Node, Map, Memo) ->
  substitute(Node, Map, Memo, fun(N, S, M) -> ty_tuple:substitute(N, S, M) end).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

empty_0tuple_test() ->
  Tuple = {node,{ty_tuple,0,[]},{terminal,0},{terminal,1}},
  true = is_empty(Tuple),
  ok.

-endif.
