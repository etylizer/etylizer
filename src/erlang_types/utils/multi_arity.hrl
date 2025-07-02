-ifndef(MULTIARITY).
-define(MULTIARITY, dnf_ty_function).
-endif.

-type type() :: {?MULTIARITY:type(), #{non_neg_integer() => ?MULTIARITY:type()}}.
-type set_of_constraint_sets() :: contraint_set:set_of_constraint_sets().
-type monomorphic_variables() :: etally:monomorphic_variables().
-type ast_ty() :: ast:ty().
-type variable() :: ty_variable:type().
-type all_variables_cache() :: term(). % TODO

-export([
  compare/2,
  singleton/2,
  any/0,
  empty/0,
  negate/1,
  union/2,
  intersect/2,
  difference/2,
  is_empty/2,
  normalize/3,
  unparse/2,
  all_variables/2
]).

-spec compare(T, T) -> eq | lt | gt when T :: type().
compare({D, M}, {D2, M2}) ->
  case ?MULTIARITY:compare(D, D2) of
    eq ->
      case maps:size(M) < maps:size(M2) of
        true -> lt;
        _ ->
          case maps:size(M) > maps:size(M2) of
            true -> gt;
            _ ->
              lists:foldl(
                fun({{_, A}, {_, B}}, eq) -> ?MULTIARITY:compare(A, B); (_, R) -> R end, 
                eq, 
                lists:zip(maps:to_list(M), maps:to_list(M2))
              )
          end
      end;
    R -> R
  end.

-spec empty() -> type().
empty() ->
  {?MULTIARITY:empty(), #{}}.

-spec any() -> type().
any() ->
  {?MULTIARITY:any(), #{}}.

-spec is_empty(type(), T) -> {boolean, T}.
is_empty({Default, All}, ST) ->
  maybe
    {true, ST1} ?= ?MULTIARITY:is_empty(Default, ST),
    maps:fold(fun
      (_Size, _V, {false, ST0}) -> {false, ST0};
      (_Size, V, {true, ST0}) -> ?MULTIARITY:is_empty(V, ST0) 
    end, {true, ST1}, All)
  end.

-spec singleton(non_neg_integer(), ?MULTIARITY:type()) -> type().
singleton(Length, Dnf) when is_integer(Length) ->
  remove_redundant({?MULTIARITY:empty(), #{Length => Dnf}}).

-spec negate(T) -> T when T :: type().
negate({Default, Ty}) ->
  remove_redundant({?MULTIARITY:negate(Default), maps:map(fun(_K,V) -> ?MULTIARITY:negate(V) end, Ty)}).

-spec union(T, T) -> T when T :: type().
union({DefaultF1, F1}, {DefaultF2, F2}) ->
  % get all keys
  AllKeys = maps:keys(F1) ++ maps:keys(F2),
  UnionKey = fun(Key) ->
    ?MULTIARITY:union(
      maps:get(Key, F1, DefaultF1),
      maps:get(Key, F2, DefaultF2)
    )
                 end,
  remove_redundant({?MULTIARITY:union(DefaultF1, DefaultF2), maps:from_list([{Key, UnionKey(Key)} || Key <- AllKeys])}).

-spec intersect(T, T) -> T when T :: type().
intersect({DefaultF1, F1}, {DefaultF2, F2}) ->
  % get all keys
  AllKeys = maps:keys(F1) ++ maps:keys(F2),
  IntersectKey = fun(Key) ->
    ?MULTIARITY:intersect(
      maps:get(Key, F1, DefaultF1),
      maps:get(Key, F2, DefaultF2)
    )
                 end,
  remove_redundant({?MULTIARITY:intersect(DefaultF1, DefaultF2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}).

-spec difference(T, T) -> T when T :: type().
difference({DefaultF1, F1}, {DefaultF2, F2}) ->
  % get all keys
  AllKeys = maps:keys(F1) ++ maps:keys(F2),
  DifferenceKey = fun(Key) ->
    ?MULTIARITY:difference(
      maps:get(Key, F1, DefaultF1),
      maps:get(Key, F2, DefaultF2)
    )
                 end,
  remove_redundant({?MULTIARITY:difference(DefaultF1, DefaultF2), maps:from_list([{Key, DifferenceKey(Key)} || Key <- AllKeys])}).

% removes mappings in others which are syntactically equivalent to the default value
-spec remove_redundant(T) -> T when T :: type().
remove_redundant({Default, Others}) ->
  {
    Default,
    #{Arity => TypeOfArity || Arity := TypeOfArity <- Others, TypeOfArity /= Default}
  }.

-spec normalize(type(), monomorphic_variables(), T) -> {set_of_constraint_sets(), T}.
normalize({Default, All}, Fixed, ST) ->
  {Others, ST2} = 
    maps:fold(fun(_Size, V, {Acc, ST0}) -> % FIXME shortcut behavior
      {Res, ST1} = ?MULTIARITY:normalize(V, Fixed, ST0),
      {constraint_set:meet(Acc, Res, Fixed), ST1}
              end, {[[]], ST}, All),

  % {DF, ST2} = ?MULTIARITY:normalize({default, maps:keys(All)}, Default, Fixed, ST2),
  {DF, ST2} = ?MULTIARITY:normalize(Default, Fixed, ST2),

  {constraint_set:meet(DF, Others, Fixed), ST2}.

-spec unparse(type(), T) -> {ast_ty(), T}.
unparse({Default, T}, ST0) ->
  {X1, ST1} = ?MULTIARITY:unparse(Default, ST0),

  {Xs, ST2} =
  lists:foldl(fun({_Size, TT}, {Cs, ST00}) -> 
    case ?MULTIARITY:unparse(TT, ST00) of
      {{predef, any}, _} -> error(todo_multi_unparse); %AnyTupleI(Size);
      {X, ST01} -> {Cs ++ [X], ST01}
    end
  end, {[], ST1}, maps:to_list(T)),

  {ast_lib:mk_union([ 
    ast_lib:mk_diff( 
      X1, 
      ast_lib:mk_union(Xs)
    ), 
    ast_lib:mk_union(Xs)
  ]), ST2}.

-spec all_variables(type(), all_variables_cache()) -> sets:set(variable()).
all_variables({Default, All}, Cache) ->
  V1 = ?MULTIARITY:all_variables(Default, Cache),
  ResVars = 
    maps:fold(fun(_Size, V, VarAcc) -> 
      Res = ?MULTIARITY:all_variables(V, Cache),
      sets:union(VarAcc, Res)
              end, sets:new(), All),
  sets:union(V1, ResVars).

