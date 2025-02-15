-module(tally_config_tests).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, tfun1/2, trange/2,
                   tunion/1, tunion/2, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0,
                   tint/0, tint/1, ttuple1/1, tinter/1, tinter/2, tlist/1, tempty_list/0,
                   tfloat/0, tfun2/3, tnot/1, tbool/0,
                   tmap/1, tmap_any/0, tmap_field_opt/2, tmap_field_req/2
                  ]).

filtermap_test_() ->
  {timeout, 15, {"filtermap", fun() ->
    ecache:reset_all(),
    {ok, [Cons]} = file:consult("test_files/tally/filtermap_hard.config"),
    {ok, [Tab]} = file:consult("test_files/tally/filtermap_hard.symtab"),
    test_utils:test_tally_satisfiable( true, Cons, [], Tab),
    ok
                                         end}}.
tatom_test_() ->
  {timeout, 15, {"guard", fun() ->
    ecache:reset_all(),
    {ok, [Cons]} = file:consult("test_files/tally/tatom.config"),
    {ok, [Tab]} = file:consult("test_files/tally/tatom.symtab"),
    test_utils:test_tally_satisfiable( true, Cons, [], Tab),
    ok
                                         end}}.

guard_test_() ->
  {timeout, 15, {"guard", fun() ->
    ecache:reset_all(),
    {ok, [Cons]} = file:consult("test_files/tally/guards.config"),
    {ok, [Tab]} = file:consult("test_files/tally/guards.symtab"),

    test_utils:test_tally_satisfiable(
      true,
      Cons,
      [],
      Tab
    ),
    ok
                                         end}}.

plus_test_() ->
  {timeout, 15, {"chained_plus", fun() ->
    ecache:reset_all(),
    {ok, [Cons]} = file:consult("test_files/tally/plus_chained.config"),

    test_utils:test_tally_satisfiable(
      true,
      Cons,
      [],
      symtab:empty()
    ),
    ok
                                         end}}.

fun_local_own_test_() ->
  {timeout, 15, {"fun_local_02_plus", fun() ->
    ecache:reset_all(),
    {ok, [Cons]} = file:consult("test_files/tally/fun_local_02_plus.config"),

    % to print out cduce command
    % io:format(user, "~s~n", [test_utils:ety_to_cduce_tally(Cons)]),

    test_utils:test_tally(
      Cons,
      test_utils:solutions(50)
    ),
    ok
                                         end}}.

% TODO timeout
%recursive_test_() ->
%  {timeout, 15, {"user_07", fun() ->
%    ecache:reset_all(),
%    {ok, [Cons]} = file:consult("test_files/tally/user_07.config"),
%
%    % to print out cduce command
%    % io:format(user, "~s~n", [test_utils:ety_to_cduce_tally(Cons)]),
%
%    test_utils:test_tally(
%      Cons,
%      test_utils:solutions(1)
%    ),
%    ok
%                                         end}}.

% symtab usage
% eval_test_() ->
%   {timeout, 150, {"eval_tally_1", fun() ->
%     ecache:reset_all(),
%     {ok, [Cons]} = file:consult("test_files/tally/eval_tally_1_cduce.config"),
%     {ok, [Symtab]} = file:consult("test_files/tally/eval_tally_1.symtab"),
%     Vars = lists:foldl(fun({S, T}, Acc) -> (ty_rec:all_variables(ast_lib:ast_to_erlang_ty(S, Symtab)) ++ ty_rec:all_variables(ast_lib:ast_to_erlang_ty(T, Symtab)) ++ Acc) end, [], Cons),
%     VarOrder = lists:map(fun(V) -> {var, Name} = ast_lib:erlang_ty_var_to_var(V), Name end,lists:sort(lists:flatten(Vars))),

%     % to print out cduce command
%     % io:format(user, "~s~n", [test_utils:ety_to_cduce_tally(Cons, VarOrder)]),

%     test_utils:test_tally(
%       VarOrder,
%       Cons,
%       Symtab,
%       test_utils:solutions(1)
%     ),
%     ok
%                                          end}}
% .