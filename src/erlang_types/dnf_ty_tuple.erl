-module(dnf_ty_tuple).

-define(P, {bdd_bool, ty_tuple}).
-define(F(Z), fun() -> Z end).


-export([equal/2, compare/2]).

%%
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/6, substitute/4]).

-export([tuple/1, all_variables/1, has_ref/2, transform/2]).

-type dnf_tuple() :: term().
-type ty_tuple() :: dnf_tuple(). % ty_tuple:type()
-type dnf_ty_tuple() :: term().

-spec tuple(ty_tuple()) -> dnf_ty_tuple().
tuple(TyTuple) -> gen_bdd:element(?P, TyTuple).

% ==
% type interface
% ==
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).

substitute(MkTy, TyBDD, Map, Memo) -> gen_bdd:substitute(?P, MkTy, TyBDD, Map, Memo).

union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).

is_any(B) -> gen_bdd:is_any(?P, B).
has_ref(Ty, Ref) -> gen_bdd:has_ref(?P, Ty, Ref).

% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

is_empty(TyBDD) ->
  gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).

is_empty_coclause(_Pos, _Neg, 0) -> true;
is_empty_coclause([], _Neg, 1) -> false; % TODO check correctness of this
is_empty_coclause(Pos, Neg, 1) ->
  % invariant: Pos is single tuple (simplification step required)
  BigS = ty_tuple:big_intersect(Pos),
  phi(ty_tuple:components(BigS), Neg).

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

normalize({default, _}, {terminal, 0}, [], [], _, _) -> [[]];
normalize({default, _}, {terminal, 1}, [], [], _, _) -> [];
normalize(Size, TyTuple, [], [], Fixed, M) ->
  % optimized NProd rule
  AllAny = [ty_rec:any() || _ <- lists:seq(1, Size)],
  normalize_no_vars(Size, TyTuple, AllAny, _NegatedTuples = [], Fixed, M);
normalize(Size, DnfTyTuple, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:tuple(Size, dnf_var_ty_tuple:tuple(DnfTyTuple)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:tuple(Size, dnf_var_ty_tuple:var(Var)) end, M).

normalize_no_vars(_Size, {terminal, 0}, _, _, _Fixed, _) -> [[]]; % empty
normalize_no_vars(Size, {terminal, 1}, BigS, N, Fixed, M) ->
  phi_norm(Size, BigS, N, Fixed, M);
normalize_no_vars(Size, {node, TyTuple, L_BDD, R_BDD}, BigS, Negated, Fixed, M) ->
  BigSExtended = [ty_rec:intersect(ToIntersect, Others) || {ToIntersect, Others} <- lists:zip(ty_tuple:components(TyTuple), BigS)],
  X1 = ?F(normalize_no_vars(Size, L_BDD, BigSExtended, Negated, Fixed, M)),
  X2 = ?F(normalize_no_vars(Size, R_BDD, BigS, [TyTuple | Negated], Fixed, M)),
  constraint_set:meet(X1, X2).

phi_norm(_Size, BigS, [], Fixed, M) ->
  lists:foldl(fun(S, Res) -> constraint_set:join(?F(Res), ?F(ty_rec:normalize(S, Fixed, M))) end, [], BigS);
phi_norm(Size, BigS, [Ty | N], Fixed, M) ->
  Solve = fun({Index, {_PComponent, NComponent}}, Result) ->
    constraint_set:meet(
      ?F(Result)
    ,
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
    ?F(lists:foldl(fun(S, Res) -> constraint_set:join(?F(Res), ?F(ty_rec:normalize(S, Fixed, M))) end, [], BigS))
    ,
    ?F(lists:foldl(Solve, [[]], lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty)))))
  ).


all_variables({terminal, 0}) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, Tuple, PositiveEdge, NegativeEdge}) ->
  lists:map(fun(E) -> ty_rec:all_variables(E) end, ty_tuple:components(Tuple))
    ++ all_variables(PositiveEdge)
    ++ all_variables(NegativeEdge).

transform({terminal, 0}, #{empty := F}) -> F();
transform({terminal, 1}, #{any_tuple := F}) -> F();
transform({node, Tuple, PositiveEdge, NegativeEdge}, Ops = #{negate := N, union := U, intersect := I} ) ->
  NF = ty_tuple:transform(Tuple, Ops),

  U([
    I([NF, transform(PositiveEdge, Ops)]),
    I([N(NF), transform(NegativeEdge, Ops)])
  ]).
