-module(ecache).


-export([reset_all/0]).

reset_all() ->
  ty_ref:reset(),
  ty_variable:reset(),
  ast_lib:reset(),
  ok.

