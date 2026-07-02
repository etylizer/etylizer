-module(global_state).

-export([
  init/0,
  clean/0,
  with_new_state/1
]).

-callback init() -> _.

-spec init() -> _.
init() ->
    ty_node:init(),
    ty_parser:init(),
    ty_variable:init().

-spec clean() -> _.
clean() ->
    ty_node:clean(),
    ty_parser:clean(),
    ty_variable:clean().

-spec with_new_state(fun(() -> _)) -> _.
with_new_state(Fun) ->
    clean(),
    init(),
    Fun().
