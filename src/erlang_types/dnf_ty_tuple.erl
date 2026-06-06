-module(dnf_ty_tuple).

-define(ATOM, ty_tuple).
-define(LEAF, ty_bool).
-define(NODE, ty_node).

-export([
  % exported because other types are encoded via tuples
  is_empty_line/2,
  normalize_line/3,
  all_variables_line/4,
  phi/3,
  phi_solve/5,
  phi_norm/4,
  phi_norm_solve/6,
  unparse_any/1,
  unparse_any/0
]).

-include("dnf/bdd.hrl").

-spec is_empty_line(line(), S) -> {boolean(), S} when S :: is_empty_cache().
is_empty_line({[], [], _T}, ST) -> {false, ST};
is_empty_line({[], Neg = [TNeg | _], T}, ST) ->
  % if there are only negative tuples 
  % it can still be the case that the line can be empty
  % intersect with tuple_any and continue
  Dim = length(ty_tuple:components(TNeg)),
  PosAny = ty_tuple:any(Dim),
  is_empty_line({[PosAny], Neg, T}, ST);
is_empty_line({Pos, Neg, T}, ST) ->
  ?assert_pattern(T, ?LEAF:any()), % sanity
  BigS = ty_tuple:big_intersect(Pos),
  phi(ty_tuple:components(BigS), Neg, ST).


-spec phi([ty:type()], [?ATOM:type()], S) -> {boolean(), S} when S :: is_empty_cache().
phi(BigS, [], ST) ->
  % TODO how big of a performance hit is non-shortcut behavior of the true branch?
  lists:foldl(
    fun(_, {true, ST0}) -> {true, ST0};
       (S, {false, ST0}) -> ?NODE:is_empty(S, ST0) 
    end, 
    {false, ST}, 
  BigS);
phi(BigS, [Ty | N], ST) ->
  maybe
    {false, ST1} ?= lists:foldl(fun(_S, {true, ST0}) -> {true, ST0}; (S, {false, ST0}) -> ?NODE:is_empty(S, ST0) end, {false, ST}, BigS),
    phi_fold_components(BigS, ty_tuple:components(Ty), 1, {true, ST1}, N)
  end.

phi_fold_components(_BigS, [], _Idx, Acc, _N) -> Acc;
phi_fold_components(BigS, [NComp | Rest], Idx, Acc, N) ->
    Acc1 = phi_solve(Idx, NComp, Acc, N, BigS),
    phi_fold_components(BigS, Rest, Idx + 1, Acc1, N).

-spec phi_solve(integer(), ty:type(), {boolean(), S}, [?ATOM:type()], [ty:type()]) -> {boolean(), S} when S :: is_empty_cache().
phi_solve(_, _, {false, ST2}, _, _) -> {false, ST2};
phi_solve(Index, NComponent, {true, ST2}, N, BigS) ->
    NewBigS = replace_at(Index, BigS, NComponent),
    phi(NewBigS, N, ST2).


-spec normalize_line({[T], [T], ?LEAF:type()}, monomorphic_variables(), S) -> 
    {set_of_constraint_sets(), S} when S :: normalize_cache(), T :: ?ATOM:type().
normalize_line({[], [], _T}, _Fixed, ST) -> {[], ST}; % test case for this branch: utils:set_add_many/2
normalize_line({[], Neg = [TNeg | _], T}, Fixed, ST) -> 
  Dim = length(ty_tuple:components(TNeg)),
  PosAny = ty_tuple:any(Dim),
  normalize_line({[PosAny], Neg, T}, Fixed, ST);
normalize_line({Pos, Neg, T}, Fixed, ST) -> 
  ?assert_pattern(T, ?LEAF:any()), % sanity
  BigS = ty_tuple:big_intersect(Pos),
  phi_norm(ty_tuple:components(BigS), Neg, Fixed, ST).

-spec phi_norm([ty_node:type()], [T], monomorphic_variables(), S) -> 
    {set_of_constraint_sets(), S} when S :: normalize_cache(), T :: ?ATOM:type().
phi_norm(BigS, NegList, Fixed, ST) ->
  %% Memoize phi_norm by (BigS, NegList). Pure in (BigS, NegList, Fixed); Fixed
  %% is constant for the whole normalize traversal. On the gen_constrs probe
  %% one (BigS, NegList) pair was recomputed up to 52k times — eliminating
  %% that redundancy is the structural lever (SAT-solver-style sub-problem
  %% memoization within a single normalize). The cache lives inside the
  %% ST map, so it dies when normalize returns — no global-state risk.
  Key = {phi_norm_tuple_memo, BigS, NegList},
  case ST of
    #{Key := Cached} -> {Cached, ST};
    _ ->
      {Res, ST1} = phi_norm_impl(BigS, NegList, Fixed, ST),
      {Res, ST1#{Key => Res}}
  end.

-spec phi_norm_impl([ty_node:type()], [T], monomorphic_variables(), S) ->
    {set_of_constraint_sets(), S} when S :: normalize_cache(), T :: ?ATOM:type().
phi_norm_impl(BigS, [], Fixed, ST) ->
  lists:foldl( % FIXME shortcut
    fun(S, {Res, ST0}) ->
      {R, ST1} = ty_node:normalize(S, Fixed, ST0),
      {constraint_set:join(Res, R, Fixed), ST1}
    end,
    {[], ST},
    BigS);
phi_norm_impl(BigS, [Ty | N], Fixed, ST) ->
  %% Inner fold short-circuit: once R2 = [[]] (trivially satisfied), join
  %% with anything stays [[]] — skip remaining normalize calls in BigS.
  {R1, ST0} = lists:foldl(
    fun(_S, {[[]], ST2}) -> {[[]], ST2};
       (S, {R2, ST2}) ->
         {R3, ST3} = ty_node:normalize(S, Fixed, ST2),
         {constraint_set:join(R2, R3, Fixed), ST3}
    end,
    {[], ST},
    BigS),
  %% Early-exit: if R1 is already trivially satisfied ([[]] is the unit of
  %% join), the joined result phi_norm returns is also [[]] regardless of R4.
  %% Skip the recursive phi_norm_fold_components fanout in that case — this is
  %% the dominant call count on hot scenarios.
  case R1 of
    [[]] -> {[[]], ST0};
    _ ->
      {R4, ST4} = phi_norm_fold_components(BigS, ty_tuple:components(Ty), 1,
                                           {[[]], ST0}, N, Fixed),
      {constraint_set:join(R1, R4, Fixed), ST4}
  end.

phi_norm_fold_components(_BigS, [], _Idx, Acc, _N, _Fixed) -> Acc;
%% Short-circuit on accumulator = [] (meet absorbs to [] from here on).
phi_norm_fold_components(_BigS, _Rest, _Idx, {[], ST} = Acc, _N, _Fixed) -> Acc;
phi_norm_fold_components(BigS, [NComp | Rest], Idx, Acc, N, Fixed) ->
    Acc1 = phi_norm_solve(Idx, NComp, Acc, N, BigS, Fixed),
    phi_norm_fold_components(BigS, Rest, Idx + 1, Acc1, N, Fixed).

-spec phi_norm_solve(integer(), ty_node:type(), {set_of_constraint_sets(), S}, [?ATOM:type()], [ty_node:type()], monomorphic_variables()) ->
    {set_of_constraint_sets(), S} when S :: normalize_cache().
phi_norm_solve(Index, NComponent, {Result, ST00}, N, BigS, Fixed) ->
    %% Replace BigS[Index] with `BigS[Index] - NComponent`, keep other entries.
    %% Direct linear-pass replace_at avoids the lists:zip+seq pair the prior
    %% implementation built fresh on every call.
    NewBigS = replace_at(Index, BigS, NComponent),
    {Res01, ST01} = phi_norm(NewBigS, N, Fixed, ST00),
    {constraint_set:meet(Result, Res01, Fixed), ST01}.

replace_at(1, [H | T], NComp) -> [ty_node:difference(H, NComp) | T];
replace_at(N, [H | T], NComp) when N > 1 -> [H | replace_at(N - 1, T, NComp)].

-spec all_variables_line([T], [T], ?LEAF:type(), all_variables_cache()) -> 
    sets:set(variable()) when T :: ?ATOM:type().
all_variables_line(P, N, Leaf, Cache) ->
  ?assert_pattern(Leaf, ty_bool:any()),
  sets:union(
     [ty_tuple:all_variables(F, Cache) || F <- P]
  ++ [ty_tuple:all_variables(F, Cache) || F <- N]
  ).

-spec unparse_any() -> ast:ty_tuple_any().
unparse_any() -> {tuple_any}.

-spec unparse_any(non_neg_integer()) -> ast:ty_tuple().
unparse_any(Size) ->
  {tuple, [{predef, any} || _ <- lists:seq(1, Size)]}.

