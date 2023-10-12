-module(ty_variable).

% ETS table is used to strict monotonically increment a variable ID counter
-export([setup_all/0, reset/0]).
-define(VAR_ETS, variable_counter_ets_table).

-export([equal/2, compare/2, substitute/4]).


-export([new/1, smallest/3, normalize/6]).

-record(var, {id, name}).
-type var() :: #var{id :: integer(), name :: string()}.

reset() ->
  catch ets:delete(?VAR_ETS),
  setup_all().

setup_all() ->
  ets:new(?VAR_ETS, [public, named_table]),
  ets:insert(?VAR_ETS, {variable_id, 0}).

-spec equal(var(), var()) -> boolean().
equal(Var1, Var2) -> compare(Var1, Var2) =:= 0.

-spec compare(var(), var()) -> -1 | 0 | 1.
compare(#var{id = Id1}, #var{id = Id2}) when Id1 < Id2 -> -1;
compare(#var{id = Id1}, #var{id = Id2}) when Id1 > Id2 -> +1;
compare(_, _) -> 0.

leq(#var{id = Id1}, #var{id = Id2}) -> Id1 =< Id2.

-spec new(string()) -> var().
new(Name) ->
  NewId = ets:update_counter(?VAR_ETS, variable_id, {2,1}),
  #var{id = NewId, name = Name}.

% assumption: PVars U NVars is not empty
smallest(PositiveVariables, NegativeVariables, FixedVariables) ->
  true = (length(PositiveVariables) + length(NegativeVariables)) > 0,

  % fixed variables are higher order than all non-fixed ones, will be picked last
  PositiveVariablesTagged = [{pos, V} || V <- PositiveVariables, not sets:is_element(V, FixedVariables)],
  NegativeVariablesTagged = [{neg, V} || V <- NegativeVariables, not sets:is_element(V, FixedVariables)],

  RestTagged =
    [{{delta, neg}, V} || V <- NegativeVariables, sets:is_element(V, FixedVariables)] ++
    [{{delta, pos}, V} || V <- PositiveVariables, sets:is_element(V, FixedVariables)],

  Sort = fun({_, V}, {_, V2}) -> leq(V, V2) end,
  [X | Z] = lists:sort(Sort, PositiveVariablesTagged++NegativeVariablesTagged) ++ lists:sort(Sort, RestTagged),

  {X, Z}.


single(Pol, VPos, VNeg, Ty, VarToTy) ->
  AccP = lists:foldl(fun(Var, Ty) -> ty_rec:intersect(Ty, VarToTy(Var)) end, Ty, VPos),
  AccN = lists:foldl(fun(Var, Ty) -> ty_rec:union(Ty, VarToTy(Var)) end, ty_rec:empty(), VNeg),
  S = ty_rec:diff(AccP, AccN),
  case Pol of
    true -> ty_rec:negate(S);
    _ -> S
  end.


% (NTLV rule)
normalize(Ty, PVar, NVar, Fixed, VarToTy, Mx) ->
  SmallestVar = ty_variable:smallest(PVar, NVar, Fixed),
  case SmallestVar of
    {{pos, Var}, _Others} ->
      Singled = single(true, PVar -- [Var], NVar, Ty, VarToTy ),
      [[{Var, ty_rec:empty(), Singled}]];
    {{neg, Var}, _Others} ->
      Singled = single(false, PVar, NVar -- [Var], Ty, VarToTy),
      [[{Var, Singled, ty_rec:any()}]];
    {{{delta, _}, _}, _} ->
      % part 1 paper Lemma C.3 and C.11 all fixed variables can be eliminated
      ty_rec:normalize(Ty, Fixed, Mx)
  end.

substitute(MkTy, Var, Map, _Memo) ->
%%  io:format(user, "Getting ~p from ~p~n", [Var, Map]),
  X = maps:get(Var, Map, ty_rec:variable(Var)),%, ty_rec:variable(Var)), % TODO
%%  io:format(user, "Got ~p~n", [X]),
%%  io:format(user, "Doing THE THING: ~p~n", [MkTy(X)]),
  MkTy(X).



-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  % create a fresh variable with a descriptor "A"
  _VarA = ty_variable:new("A"),
  ok.

strictly_increasing_id_test() ->
  #var{id = IdA} = ty_variable:new("A"),
  #var{id = IdB} = ty_variable:new("B"),
  #var{id = IdC} = ty_variable:new("C"),
  true = (IdA < IdB),
  true = (IdB < IdC),
  ok.

same_name_different_id_test() ->
  VarA = ty_variable:new("a"),
  VarB = ty_variable:new("a"),
  -1 = ty_variable:compare(VarA, VarB),
  ok.

-endif.
