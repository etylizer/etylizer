-module(global_state).

-export([
  init/0,
  clean/0,
  with_new_state/1
]).

-callback init() -> ok.

-spec modules_with_global_state() -> [module()].
modules_with_global_state() -> [ty_node, ty_parser, ty_variable].

-spec init() -> _.
init() ->
  lists:foreach(fun(M) -> M:init() end, modules_with_global_state()).

-spec clean() -> _.
clean() ->
  lists:foreach(fun(M) -> M:clean() end, modules_with_global_state()).

-spec with_new_state(fun(() -> _)) -> _.
with_new_state(Fun) ->
  clean(),
  init(),
  Fun().
