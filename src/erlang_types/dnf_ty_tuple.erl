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
  phi_solve/4,
  phi_norm/4,
  phi_norm_solve/5,
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
    lists:foldl(
      fun(E, Acc) -> phi_solve(E, Acc, N, BigS) end,
      {true, ST1},
      lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty))))
  end.

-spec phi_solve({integer(), {ty:type(), ty:type()}}, {boolean(), S}, [?ATOM:type()], [ty:type()]) -> {boolean(), S} when S :: is_empty_cache().
phi_solve(_, {false, ST2}, _, _) -> {false, ST2};
phi_solve({Index, {_PComponent, NComponent}}, {true, ST2}, N, BigS) ->
    % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
    DoDiff = fun({IIndex, PComp}) ->
      case IIndex of
        Index -> ?NODE:difference(PComp, NComponent);
        _ -> PComp
      end
             end,
    NewBigS = lists:map(DoDiff, lists:zip(lists:seq(1, length(BigS)), BigS)),
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
phi_norm(BigS, [], Fixed, ST) ->
  lists:foldl( % FIXME shortcut
    fun(S, {Res, ST0}) -> 
      {R, ST1} = ty_node:normalize(S, Fixed, ST0),
      {constraint_set:join(Res, R, Fixed), ST1} 
    end, 
    {[], ST}, 
    BigS);
phi_norm(BigS, [Ty | N], Fixed, ST) ->
  {R1, ST0} = lists:foldl(
    fun(S, {R2, ST2}) ->
      {R3, ST3} = ty_node:normalize(S, Fixed, ST2),
      {constraint_set:join(R2, R3, Fixed), ST3}
    end,
    {[], ST},
    BigS),

  {R4, ST4} = lists:foldl(
    fun(E, Acc) -> phi_norm_solve(E, Acc, N, BigS, Fixed) end,
    {[[]], ST0},
    lists:zip(lists:seq(1, length(ty_tuple:components(Ty))), lists:zip(BigS, ty_tuple:components(Ty)))
  ),

  {constraint_set:join(R1, R4, Fixed), ST4}.

-spec phi_norm_solve({integer(), {ty_node:type(), ty_node:type()}}, {set_of_constraint_sets(), S}, [?ATOM:type()], [ty_node:type()], monomorphic_variables()) ->
    {set_of_constraint_sets(), S} when S :: normalize_cache().
phi_norm_solve({Index, {_PComponent, NComponent}}, {Result, ST00}, N, BigS, Fixed) ->
    % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
    DoDiff =
      fun({IIndex, PComp}) ->
        case IIndex of
          Index -> ty_node:difference(PComp, NComponent);
          _ -> PComp
        end
      end,
    NewBigS = lists:map(DoDiff, lists:zip(lists:seq(1, length(BigS)), BigS)),
    {Res01, ST01} = phi_norm(NewBigS, N, Fixed, ST00),
    {constraint_set:meet(Result, Res01, Fixed), ST01}.

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

