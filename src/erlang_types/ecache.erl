-module(ecache).


-export([reset_all/0]).

reset_all() ->
  ty_ref:reset(),
  ast_lib:reset(),
  ty_variable:reset(),
  ok.

