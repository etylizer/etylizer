-module(global_state).

-compile([export_all, nowarn_export_all]).

-type state() :: term().

-callback init() -> ok.

-spec modules_with_global_state() -> [module()].
modules_with_global_state() -> [ty_node, ty_parser, ty_variable].

-spec init() -> _.
init() ->
  lists:foreach(fun(M) -> M:init() end, modules_with_global_state()).

-spec clean() -> _.
clean() ->
  lists:foreach(fun(M) -> M:clean() end, modules_with_global_state()).

-spec get_state(atom()) -> state().
get_state(Table) ->
  [{state, State}] = ets:lookup(Table, state),
  State.

-spec set_state(atom(), state()) -> ok.
set_state(Table, State) ->
  ets:insert(Table, {state, State}).
  

with_new_state(Fun) ->
  clean(),
  init(),
  Fun().