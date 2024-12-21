-module(ast_lib_tests).

-include_lib("eunit/include/eunit.hrl").
-import(stdtypes, [tmu/2, tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tunion/1, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0]).
-import(test_utils, [ty_from_term/1]).


basic_test() ->
  test_utils:reset_ets(),

  AstTy = tatom(a),
  ActualETy = ast_lib:ast_to_erlang_ty(AstTy, symtab:empty()),
  ExpectedETy = ty_from_term($a),
  true = ty_rec:is_equivalent(ActualETy, ExpectedETy),

  ast_lib:erlang_ty_to_ast(ActualETy),
  
  ok.