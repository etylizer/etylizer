-module(dnf_ty_tuple).
-vsn({2,0,0}).

-define(P, {bdd_bool, ty_tuple}).
-define(F(Z), fun() -> Z end).

-behavior(eq).
-export([equal/2, compare/2]).

%%-behavior(type).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/2, is_any/1, normalize/6, substitute/3]).

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

union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).

eval(B) -> gen_bdd:eval(?P, B).
is_any(B) -> gen_bdd:is_any(?P, B).

% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

is_empty(default, 0) -> true;
is_empty(default, {terminal, 1}) -> false;
is_empty(Size, TyBDD) -> is_empty(
  TyBDD,
  [ty_rec:any() || _ <- lists:seq(1, Size)],
  _NegatedTuples = []
).

is_empty(0, _, _) -> true;
is_empty({terminal, 1}, BigS, N) ->
  phi(BigS, N);
is_empty({node, TyTuple, L_BDD, R_BDD}, BigS, Negated) ->
  BigSExtended = [ty_rec:intersect(ToIntersect, Others) || {ToIntersect, Others} <- lists:zip(ty_tuple:components(TyTuple), BigS)],

  is_empty(L_BDD, BigSExtended, Negated)
  andalso
    is_empty(R_BDD, BigS, [TyTuple | Negated]).

phi(BigS, []) ->
  lists:foldl(fun(S, Res) -> Res orelse ty_rec:is_empty(S) end, false, BigS); % TODO unit false?
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

normalize({default, _}, 0, [], [], _, _) -> [[]];
normalize({default, _}, {terminal, 1}, [], [], _, _) -> [];
normalize(Size, TyTuple, [], [], Fixed, M) ->
  % optimized NProd rule
  AllAny = [ty_rec:any() || _ <- lists:seq(1, Size)],
  normalize_no_vars(Size, TyTuple, AllAny, _NegatedTuples = [], Fixed, M);
normalize(Size, DnfTyTuple, PVar, NVar, Fixed, M) ->
  io:format(user, "DOing the normalization for ~p with ~p~n", [Size, DnfTyTuple]),
  Ty = ty_rec:tuple(Size, dnf_var_ty_tuple:tuple(DnfTyTuple)),
  % ntlv rule
  R = ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:tuple(Size, dnf_var_ty_tuple:var(Var)) end, M),
  io:format(user, "Got ~p~n", [R]),
  R.

normalize_no_vars(_Size, 0, _, _, _Fixed, _) -> [[]]; % empty
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
            Index -> ty_rec:diff(PComp, NComponent);
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
    % TODO tomorrow chekc here again
    ?F(lists:foldl(Solve, [[]], lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty)))))
  )
.

substitute(0, _, _) -> 0;
substitute({terminal, 1}, _, _) ->
  {terminal, 1};
substitute({node, TyTuple, L_BDD, R_BDD}, Map, Memo) ->
  NewS = lists:map(fun(E) -> ty_rec:substitute(E, Map, Memo) end, ty_tuple:components(TyTuple)),

  NewTyTuple = ty_tuple:tuple(NewS),

  union(
    intersect(tuple(NewTyTuple), L_BDD),
    intersect(negate(tuple(NewTyTuple)), R_BDD)
    ).

has_ref(0, _) -> false;
has_ref({terminal, _}, _) -> false;
has_ref({node, Tuple, PositiveEdge, NegativeEdge}, Ref) ->
  ty_tuple:has_ref(Tuple, Ref)
    orelse
    has_ref(PositiveEdge, Ref)
    orelse
    has_ref(NegativeEdge, Ref).

all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, Tuple, PositiveEdge, NegativeEdge}) ->
  lists:map(fun(E) -> ty_rec:all_variables(E) end, ty_tuple:components(Tuple))
    ++ all_variables(PositiveEdge)
    ++ all_variables(NegativeEdge).

transform(0, #{empty := F}) -> F();
transform({terminal, 1}, #{any_tuple := F}) -> F();
transform({node, Tuple, PositiveEdge, NegativeEdge}, Ops = #{negate := N, union := U, intersect := I} ) ->
  NF = ty_tuple:transform(Tuple, Ops),

  U([
    I([NF, transform(PositiveEdge, Ops)]),
    I([N(NF), transform(NegativeEdge, Ops)])
  ]).
