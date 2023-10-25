-module(pretty_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tunion/1, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0]).
-import(test_utils, [is_subtype/2, is_equiv/2]).

variable_union_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a), tatom(foo)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  %io:format(user,"~s~n", [pretty:render_ty(Pretty)]),

  ok.

variable_union2_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a), tvar(b), tatom(foo)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  %io:format(user,"~s~n", [pretty:render_ty(Pretty)]),

  ok.

variable_union3_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a), tvar(b), tvar(c), tatom(foo)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  %io:format(user,"~s~n", [pretty:render_ty(Pretty)]),

  ok.

variable_union4_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a), tvar(b), tvar(c), tvar(d), tatom(foo)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  %io:format(user,"~s~n", [pretty:render_ty(Pretty)]),

  ok.


other_test() ->
  ecache:reset_all(),
  V0 = tunion([
    ttuple([tintersect([tatom(b), tvar(a5)]), tatom(int)]),
    ttuple([tatom(a), tatom(int)]),
    tintersect([
      tunion([
        ttuple([tintersect([tatom(b), tvar(a5)]), tatom(int)]),
        ttuple([tatom(a), tatom(int)])
      ]),
      tvar(a0a0)
    ])
  ]),
  B = ast_lib:ast_to_erlang_ty(V0),
  Pretty = ast_lib:erlang_ty_to_ast(B),

  true = subty:is_equivalent(none, V0, Pretty),
  io:format(user,"~s~n", [pretty:render_ty(Pretty)]),

  ok.
