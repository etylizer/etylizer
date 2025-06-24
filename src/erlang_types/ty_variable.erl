-module(ty_variable).

-define(VAR_ETS, variable_counter_ets_table).
-define(ALL_ETS, [?VAR_ETS]).

-spec init() -> _.
init() ->
  case ets:whereis(?VAR_ETS) of
      undefined -> 
        [ets:new(T, [public, set, named_table]) || T <- ?ALL_ETS],
        ets:insert(?VAR_ETS, {variable_id, 0});
      _ -> ok
  end.

-spec clean() -> _.
clean() ->
  case ets:whereis(?VAR_ETS) of
      undefined -> ok;
      _ -> 
        [ets:delete(T) || T <- ?ALL_ETS]
  end.

% variables have either their name as their ID (coming from a ast_lib conversion)
% or a unique ID (usually generated inside the erlang_types library)
-record(var, {id, name}).
-type var() :: 
  #var{id :: integer() | name, name :: atom()}.

-spec equal(var(), var()) -> boolean().
equal(Var1, Var2) -> compare(Var1, Var2) =:= eq.

-spec compare(var(), var()) -> lt | eq | gt.
compare(#var{id = name, name = N1}, #var{id = name, name = N2}) ->
  case {N1 > N2, N1 < N2} of
    {false, false} -> eq;
    {true, _} -> gt;
    {_, true} -> lt
  end;
compare(#var{id = name}, #var{}) -> lt;
compare(#var{}, #var{id = name}) -> gt;
compare(#var{id = Id1}, #var{id = Id2}) when Id1 < Id2 -> lt;
compare(#var{id = Id1}, #var{id = Id2}) when Id1 > Id2 -> gt;
compare(_, _) -> eq.

leq(V1, V2) -> 
  compare(V1, V2) /= gt.

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

unparse(#var{id = name, name = Name}, C) ->
  {{var, Name}, C};
unparse(#var{id = Id, name = Name}, C) ->
  {{var, list_to_atom("$ety_" ++ integer_to_list(Id) ++ "_" ++ atom_to_list(Name))}, C}.

% % assumption: PVars U NVars is not empty
% smallest(PositiveVariables, NegativeVariables, FixedVariables) ->
%   true = (length(PositiveVariables) + length(NegativeVariables)) > 0,

%   % fixed variables are higher order than all non-fixed ones, will be picked last
%   PositiveVariablesTagged = [{pos, V} || V <- PositiveVariables, not sets:is_element(V, FixedVariables)],
%   NegativeVariablesTagged = [{neg, V} || V <- NegativeVariables, not sets:is_element(V, FixedVariables)],

%   RestTagged =
%     [{{delta, neg}, V} || V <- NegativeVariables, sets:is_element(V, FixedVariables)] ++
%     [{{delta, pos}, V} || V <- PositiveVariables, sets:is_element(V, FixedVariables)],

%   Sort = fun({_, V}, {_, V2}) -> leq(V, V2) end,
%   [X | Z] = lists:sort(Sort, PositiveVariablesTagged++NegativeVariablesTagged) ++ lists:sort(Sort, RestTagged),

%   {X, Z}.


% single(Pol, VPos, VNeg, Ty, VarToTy) ->
%   AccP = lists:foldl(fun(Var, TTy) -> ty_rec:intersect(TTy, VarToTy(Var)) end, Ty, VPos),
%   AccN = lists:foldl(fun(Var, TTy) -> ty_rec:union(TTy, VarToTy(Var)) end, ty_rec:empty(), VNeg),
%   S = ty_rec:diff(AccP, AccN),
%   case Pol of
%     true -> ty_rec:negate(S);
%     _ -> S
%   end.


% % (NTLV rule)
% normalize_corec(Ty, PVar, NVar, Fixed, VarToTy, Mx) ->
%   SmallestVar = ty_variable:smallest(PVar, NVar, Fixed),
%   case SmallestVar of
%     {{pos, Var}, _Others} ->
%       Singled = single(true, PVar -- [Var], NVar, Ty, VarToTy ),
%       [[{Var, ty_rec:empty(), Singled}]];
%     {{neg, Var}, _Others} ->
%       Singled = single(false, PVar, NVar -- [Var], Ty, VarToTy),
%       [[{Var, Singled, ty_rec:any()}]];
%     {{{delta, _}, _}, _} ->
%       % part 1 paper Lemma C.3 and C.11 all fixed variables can be eliminated
%       ty_rec:normalize_corec(Ty, Fixed, Mx)
%   end.

% substitute(MkTy, Var, Map, _Memo) ->
%   X = maps:get(Var, Map, ty_rec:variable(Var)),
%   MkTy(X).

% all_variables(Var, _) -> [Var].
% raw_transform(T, Op) -> transform(T, Op).
% transform(Ty, #{var := ToVar}) -> ToVar(Ty).
