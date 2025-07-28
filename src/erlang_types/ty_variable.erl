-module(ty_variable).

-define(VAR_ETS, variable_counter_ets_table).
-define(ALL_ETS, [?VAR_ETS]).

-export([
  init/0,
  clean/0
]).

-export([
  equal/2,
  compare/2,
  leq/2,
  fresh_from/1,
  new_with_name/1,
  unparse/2,
  with_name_and_id/2
]).

-export_type([type/0]).


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
-opaque type() :: #var{id :: integer() | name, name :: atom()}.

-spec equal(type(), type()) -> boolean().
equal(Var1, Var2) -> compare(Var1, Var2) =:= eq.

-spec compare(type(), type()) -> lt | eq | gt.
compare(#var{id = name, name = N1}, #var{id = name, name = N2}) ->
  % natural order for $ variables
  case {id_of(N1), id_of(N2)} of
    {{id, Id1}, {id, Id2}} -> 
      compare(#var{id = Id1}, #var{id = Id2});
    _ ->
      case {N1 > N2, N1 < N2} of
        {false, false} -> eq;
        {true, _} -> lt;
        {_, true} -> gt
      end 
  end;
compare(#var{id = name}, #var{}) -> gt;
compare(#var{}, #var{id = name}) -> lt;
compare(#var{id = Id1}, #var{id = Id2}) when Id1 < Id2 -> gt;
compare(#var{id = Id1}, #var{id = Id2}) when Id1 > Id2 -> lt;
compare(_, _) -> eq.

id_of(Name) when is_atom(Name) ->
  case atom_to_list(Name) of
    [$$ | Rest] ->
      try list_to_integer(Rest) of
        Int -> {id, Int}
      catch
        error:badarg -> none
      end;
    _ -> 
      none
  end;
id_of(_) -> none.

-spec leq(type(), type()) -> boolean().
leq(V1, V2) -> 
  (compare(V1, V2) == eq) orelse (compare(V1, V2) == lt).

-spec fresh_from(type()) -> type().
fresh_from(#var{id = name, name = Name}) ->
  Id = get_new_id(),
  #var{id = Id, name = Name};
fresh_from(#var{id = _Id, name = Name}) ->
  new(Name).

-spec new(atom()) -> type().
new(Name) when is_atom(Name) ->
  NewId = ets:update_counter(?VAR_ETS, variable_id, {2,1}),
  #var{id = NewId, name = Name}.

-spec new_with_name(atom()) -> type().
new_with_name(Name) when is_atom(Name) ->
  #var{id = name, name = Name}.

% used in ty_parser to convert already known variables
-spec with_name_and_id(integer(), atom()) -> type().
with_name_and_id(Id, Name) when is_atom(Name) ->
  #var{id = Id, name = Name}.

-spec get_new_id() -> non_neg_integer().
get_new_id() ->
  ets:update_counter(?VAR_ETS, variable_id, {2,1}).

-spec unparse(type(), ST) -> {ast:ty(), ST}.
unparse(#var{id = name, name = Name}, C) ->
  {{var, Name}, C};
unparse(#var{id = Id, name = Name}, C) ->
  {{var, list_to_atom("$ety_" ++ integer_to_list(Id) ++ "_" ++ atom_to_list(Name))}, C}.

