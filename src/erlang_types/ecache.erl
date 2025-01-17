-module(ecache).


-export([reset_all/0]).

reset_all() ->
  ty_ref:reset(),
  ast_lib:reset(),
  ast_to_erlang_ty:reset(),
  ty_variable:reset(),
  ok.

