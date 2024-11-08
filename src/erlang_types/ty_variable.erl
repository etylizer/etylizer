-module(ty_variable).

% ETS table is used to strict monotonically increment a variable ID counter
-export([setup_all/0, reset/0]).
-define(VAR_ETS, variable_counter_ets_table).

-export([hash/1, update_id/1, compare/2, equal/2, substitute/4, has_ref/2, all_variables/2, name/1]).


-export([fresh_from/1, new/1, new_with_name/1, new_with_name_and_id/2, smallest/3, normalize_corec/6, raw_transform/2, transform/2, get_new_id/0]).

-export_type([var/0]).

% variables have either their name as their ID (coming from a ast_lib conversion)
%  or a unique ID (usually generated inside the erlang_types library)
-record(var, {id, name}).
-type var() :: 
  #var{id :: integer() | name, name :: atom()}.

hash(Var) -> erlang:phash2(Var).

reset() ->
  catch ets:delete(?VAR_ETS),
  setup_all().

setup_all() ->
  ets:new(?VAR_ETS, [public, named_table]),
  ets:insert(?VAR_ETS, {variable_id, 0}).

-spec equal(var(), var()) -> boolean().
equal(Var1, Var2) -> compare(Var1, Var2) =:= 0.

-spec compare(var(), var()) -> -1 | 0 | 1.
compare(#var{id = name, name = N1}, #var{id = name, name = N2}) ->
  case {N1 > N2, N1 < N2} of
    {false, false} -> 0;
    {true, _} -> +1;
    {_, true} -> -1
  end;
compare(#var{id = name}, #var{}) -> -1;
compare(#var{}, #var{id = name}) -> +1;
compare(#var{id = Id1}, #var{id = Id2}) when Id1 < Id2 -> -1;
compare(#var{id = Id1}, #var{id = Id2}) when Id1 > Id2 -> +1;
compare(_, _) -> 0.

leq(V1, V2) -> 
  compare(V1, V2) < 1.

has_ref(_, _) -> false.

update_id(Id) ->
	ets:update_counter(?VAR_ETS, variable_id, {2, Id}).

fresh_from(#var{id = name, name = Name}) ->
  Id = get_new_id(),
  #var{id = Id, name = Name};
fresh_from(#var{id = _Id, name = Name}) ->
  new(Name).

-spec name(var()) -> atom().
name(#var{name = Name}) -> Name.

-spec new(atom()) -> var().
new(Name) when is_atom(Name) ->
  NewId = ets:update_counter(?VAR_ETS, variable_id, {2,1}),
  #var{id = NewId, name = Name}.

-spec new_with_name(atom()) -> var().
new_with_name(Name) when is_atom(Name) ->
  #var{id = name, name = Name}.

new_with_name_and_id(Id, Name) when is_atom(Name) ->
  Current = ets:update_counter(?VAR_ETS, variable_id, {2,0}),
  false = (Current < Id),
  #var{id = Id, name = Name}.

get_new_id() ->
  ets:update_counter(?VAR_ETS, variable_id, {2,1}).

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
  AccP = lists:foldl(fun(Var, TTy) -> ty_rec:intersect(TTy, VarToTy(Var)) end, Ty, VPos),
  AccN = lists:foldl(fun(Var, TTy) -> ty_rec:union(TTy, VarToTy(Var)) end, ty_rec:empty(), VNeg),
  S = ty_rec:diff(AccP, AccN),
  case Pol of
    true -> ty_rec:negate(S);
    _ -> S
  end.


% (NTLV rule)
normalize_corec(Ty, PVar, NVar, Fixed, VarToTy, Mx) ->
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
      ty_rec:normalize_corec(Ty, Fixed, Mx)
  end.

substitute(MkTy, Var, Map, _Memo) ->
  X = maps:get(Var, Map, ty_rec:variable(Var)),
  MkTy(X).

all_variables(Var, _) -> [Var].
raw_transform(T, Op) -> transform(T, Op).
transform(Ty, #{var := ToVar}) -> ToVar(Ty).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  % create a fresh variable with a descriptor "A"
  _VarA = ty_variable:new(a),
  ok.

strictly_increasing_id_test() ->
  #var{id = IdA} = ty_variable:new(a),
  #var{id = IdB} = ty_variable:new(b),
  #var{id = IdC} = ty_variable:new(c),
  true = (IdA < IdB),
  true = (IdB < IdC),
  ok.

same_name_different_id_test() ->
  VarA = ty_variable:new(a),
  VarB = ty_variable:new(a),
  -1 = ty_variable:compare(VarA, VarB),
  ok.

same_name_same_id_test() ->
  VarA = ty_variable:new_with_name(a),
  VarB = ty_variable:new_with_name(a),
  0 = ty_variable:compare(VarA, VarB),
  ok.

-endif.

