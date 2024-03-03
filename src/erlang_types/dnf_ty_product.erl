-module(dnf_ty_product).

-define(F(Z), fun() -> Z end).

-export([is_empty/1, normalize/6, substitute/4]).
-export([tuple/1, all_variables/1, transform/2]).
-export([has_ref/2, any/0, empty/0, equal/2, union/2, intersect/2, negate/1, diff/2, compare/2, phi/2]).

-include_lib("sanity.hrl").

-define(T, top_2tuple).
-define(B, []).

any() -> ?T.
empty() -> ?B.

% syntactic equality
equal(?T, ?T) -> true;
equal(?T, _) -> false;
equal(_, ?T) -> false;
equal(A, A) -> true;
equal(_, _) -> false.
% dummy not needed
compare(X, X) -> 0;
compare(X, Y) -> case X < Y of true -> -1; _ -> 1 end.

union(?T, _) -> ?T;
union(_, ?T) -> ?T;
union(?B, B) -> B;
union(B, ?B) -> B;
union(B, B) -> B;
union(A, B) -> 
  X = A ++ B,
  Dnf = [{_Pi = [{S, T}], _Ni = []} || {ty_tuple, 2, [S, T]} <- X],
  Res = normal_cduce(Dnf),
  [{ty_tuple, 2, [T1, T2]} || {T1, T2} <- Res].
   

intersect(?T, B) -> B;
intersect(B, ?T) -> B;
intersect(?B, _) -> ?B;
intersect(_, ?B) -> ?B;
intersect(A, A) -> A;
intersect(A, B) -> 
  negate(union(negate(A), negate(B))).

negate(?T) -> ?B;
negate(?B) -> ?T;
negate(A) ->
  % Partitioning:
  %    (t,s) - ((t1,s1) | (t2,s2) | ... | (tn,sn))
  %     =
  %     (t & t1, s - s1) | ... | (t & tn, s - sn) | (t - (t1|...|tn), s)
  % Negation:
  % (Any, Any) - ((t1,s1) | ... |(tn,sn))
  % = (Any & t1, Any - s1) | ... | (Any & tn, Any - sn) | (Any - (t1|...|tn), Any)
  % = (t1, !s1) | ... | (tn, !sn) | (!(t1|...|tn), Any)
  ?TIME(negate_2_tuple, negate(2, A)).
  

negate(2, A) ->
  io:format(user,"NEGATE TUPLE ~p~n", [A]),
  R = normal_cduce([_SingleCoClause = {_P = [{ty_rec:any(), ty_rec:any()}], _N = [{S, T} || {ty_tuple, 2, [S, T]} <- A]}]),
  io:format(user,"RESULT NEGATE TUPLE ~p~n", [R]),
  [{ty_tuple, 2, [T1, T2]} || {T1, T2} <- R].


diff(A, B) -> 
  intersect(A, negate(B)).

all_variables(?T) -> [];
all_variables(?B) -> [];
all_variables(Ty) ->
  SS = fun(Tuple) -> ty_tuple:all_variables(Tuple) end,
  lists:usort(lists:flatten([SS(T) || T <- Ty])).

has_ref(?T, _Ref) -> false;
has_ref(?B, _Ref) -> false;
has_ref(Ty, Ref) ->
  lists:any(fun(E) -> ty_tuple:has_ref(E, Ref) end, Ty).

substitute(?T, _Map, _Memo,_) -> ?T;
substitute(?B, _Map, _Memo,_) -> ?B;
substitute(Dnf, Map, Memo, _) -> 
  [ty_tuple:substitute(T, Map, Memo) || T <- Dnf].

dnf(?T, {_ProcessCoclause, _CombineResults}) -> error(todo1);
dnf(?B, {ProcessCoclause, _CombineResults}) -> error(todo2), ProcessCoclause({[], [], 0});
dnf([C | Cs], {ProcessCoclause, CombineResults}) ->
  Ini = ProcessCoclause({[C], [], 1}),
  lists:foldl(
    fun(E,Acc) -> 
      CombineResults(?F(ProcessCoclause({[E], [], 1})), ?F(Acc)) 
  end, 
  Ini,
  Cs).
 
transform(?T, #{any := Any}) -> Any();
transform(?B, #{empty := None}) -> None();
transform(Dnf, Ops = #{union := Union, to_tuple := ToTuple}) -> 
  io:format(user,"~p~n", [Dnf]),
  SS = fun({ty_tuple, 2, Components}) -> ToTuple(Components) end,
  Union([SS(C) || C <- Dnf])
.

tuple(TyTuple) -> [TyTuple].

is_empty(?T) -> false;
is_empty(?B) -> true;
is_empty(TyBDD) -> 
  Res = dnf(TyBDD, {fun is_empty_coclause/1, fun is_empty_union/2}),
  Res.

is_empty_union(F1, F2) ->
  F1() andalso F2().

% TODO replace n-tuple implementation with simple 2-tuple implementation
is_empty_coclause({Pos, Neg, T}) ->
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
    fun({Pos, Neg, T}) ->
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


% =================
% CDuce code border

normal_cduce(X) ->
  cleanup(lists:foldl(fun line/2, [], X)).

cleanup(L) ->
  Aux = fun A({T1, T2}, Accu) ->
    case Accu of
      [] -> [{T1, T2}];
      [{S1, S2} | Rem] -> 
        case ty_rec:is_equivalent(T2, S2) of
          true -> [{ty_rec:union(S1, T1), S2}| Rem];
          _ -> [{S1, S2} | A({T1, T2}, Rem)]
        end
    end
  end,
  lists:foldl(Aux, [], L).

bigcap(T1, T2, []) -> {T1, T2};
bigcap(T1, T2, [{S1, S2} | Rem]) -> 
  bigcap(ty_rec:intersect(T1, S1), ty_rec:intersect(T2, S2), Rem).

line({P, N}, Accu) ->
  {D1, D2} = bigcap(ty_rec:any(), ty_rec:any(), P),
  case not (ty_rec:is_empty(D1) orelse ty_rec:is_empty(D2)) of
    true -> 
      Resid = make_ref(), put(Resid, ty_rec:empty()),
      F = fun({T1, T2}, FAccu) -> 
        I = ty_rec:intersect(D1, T1),
        case not ty_rec:is_empty(I) of
          true ->
            put(Resid, ty_rec:union(get(Resid), T1)),
            T2new = ty_rec:diff(D2, T2),
            case not ty_rec:is_empty(T2new) of
              true -> add([], I, T2new, FAccu);
              _ -> FAccu 
            end;
          _ -> 
            FAccu
        end
      end,

      NewAccu = lists:foldl(F, Accu, normal(N)),
      NewD1 = ty_rec:diff(D1, get(Resid)),
      case not ty_rec:is_empty(NewD1) of
        true -> add([], NewD1, D2, NewAccu);
        _ -> NewAccu
      end;
    _ -> Accu
  end.


normal(X) ->
  lists:foldl(fun({T1, T2}, Accu) -> 
    add([], T1, T2, Accu) 
  end, [], X).

add(Root, T1, T2, []) ->
  [{T1, T2} | Root];
add(Root, T1, T2, [{S1, S2} | Rem]) ->
  I = ty_rec:intersect(T1, S1),
  case ty_rec:is_empty(I) of
    true -> add([{S1, S2} | Root], T1, T2, Rem);
    _ ->
      NewRoot = [{I, ty_rec:union(T2, S2)} | Root],
      K = ty_rec:diff(S1, T1),
      NewRoot2 = case not ty_rec:is_empty(K) of
        true -> [{K, S2} | NewRoot];
        _ -> NewRoot
      end,
      J = ty_rec:diff(T1, S1),
      case not ty_rec:is_empty(J) of
        true -> add(NewRoot2, J, T2, Rem);
        _ -> 
          lists:reverse(NewRoot2) ++ Rem
      end
  end.

