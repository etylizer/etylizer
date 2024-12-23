-module(ast_check_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("kernel/include/logger.hrl").

mk_test_ty(T) ->
    Loc = {1,1},
    {type,
     Loc,
     tuple,
     [{atom,Loc,call},
      {user_type,Loc,anno,[]},
      T,
      {type,
       Loc,
       list,
       [T]}]}.

inst_ty_test() ->
    Loc = {1,1},
    TyArg = {user_type, Loc, guard_test,[]},
    TyVar = {var, Loc, 'T'},
    ?assertEqual(mk_test_ty(TyArg), ast_check:inst_ty(['T'], [TyArg], mk_test_ty(TyVar))).

lookup_ty_test() ->
    Loc = {1,1},
    TyArg = {user_type, Loc, guard_test,[]},
    TyVar = {var, Loc, 'T'},
    Attr = {attribute,
            Loc,
            type,
            {gen_funcall, mk_test_ty(TyVar), [{var,Loc,'T'}]}},
    M = ast_check:prepare_spec(ast_erl, [Attr]),
    ?LOG_DEBUG("M = ~p", [M]),
    ?assertEqual(mk_test_ty(TyArg), ast_check:lookup_ty_or_die(M, ast_erl, 'gen_funcall', [TyArg])).

lookup_ty_realworld_test() ->
    Forms = parse:parse_file_or_die("src/ast_erl.erl"),
    M = ast_check:prepare_spec(ast_erl, Forms),
    ?LOG_DEBUG("Forms = ~p", [Forms]),
    ?LOG_DEBUG("M = ~p", [M]),
    TyArg = {user_type, {1,1}, guard_test,[]},
    T = ast_check:lookup_ty_or_die(M, ast_erl, 'gen_funcall', [TyArg]),
    ?assertMatch({type, _, tuple, _}, T).

check_realworld_test() ->
    Forms = parse:parse_file_or_die("src/ast_erl.erl"),
    M = ast_check:prepare_spec(ast_erl, Forms),
    true = ast_check:check(M, ast_erl, "test_files/ast_check_test.erl").

check_against(TyName, X) ->
    Forms = parse:parse_file_or_die("src/ast_erl.erl"),
    M = ast_check:prepare_spec(ast_erl, Forms),
    Ty = ast_check:lookup_ty_or_die(M, ast_erl, TyName, []),
    true = ast_check:check_against_type(M, ast_erl, Ty, X).

check_antidote1_test() ->
    Exp0 =
        {'fun',
         {47,19},
         {function,
          {atom,{47,23},riak_core},
          {atom,{47,33},staged_join},
          {integer,{47,45},1}}},
    check_against(exp, Exp0).

check_antidote2_test() ->
    Exp = {match,
           {208,21},
           {var,{208,21},'Msg'},
           {op,
            {209,25},
            '++',
            {var,{208,27},'ConfigPrefix'},
            {op,
             {210,25},
             '++',
             {string,
              {209,28},
              ".throttle tiers must include a tier with "},
             {op,
              {211,25},
              '++',
              {var,
               {210,28},
               'LoadFactorMeasure'},
              {string,{211,28}," 0"}}}}},
    check_against(exp, Exp).

check_riak_test() ->
    Exp = {op,
           {205,19},
           '-',
           {integer,{205,20},1}},
    check_against(pat, Exp).
