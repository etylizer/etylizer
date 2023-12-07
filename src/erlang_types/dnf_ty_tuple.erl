-module(dnf_ty_tuple).

-define(P, {bdd_bool, ty_tuple}).
-define(F(Z), fun() -> Z end).

-export([equal/2, compare/2]).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/6, substitute/4]).
-export([tuple/1, all_variables/1, has_ref/2, transform/2]).

tuple(TyTuple) -> gen_bdd:element(?P, TyTuple).

empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).
all_variables(TyBDD) -> gen_bdd:all_variables(?P, TyBDD).
substitute(MkTy, TyBDD, Map, Memo) -> gen_bdd:substitute(?P, MkTy, TyBDD, Map, Memo).
union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).
is_any(B) -> gen_bdd:is_any(?P, B).
has_ref(Ty, Ref) -> gen_bdd:has_ref(?P, Ty, Ref).
equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).
transform(Ty, Ops) -> gen_bdd:transform(?P, Ty, Ops).

is_empty(TyBDD) ->
  gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).

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
  gen_bdd:dnf(?P, Ty, {
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

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

empty_0tuple_test() ->
  Tuple = {node,{ty_tuple,0,[]},{terminal,0},{terminal,1}},
  true = is_empty(Tuple),
  ok.

-endif.
