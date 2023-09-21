-module(typing_test).

-include_lib("eunit/include/eunit.hrl").
-include_lib("log.hrl").

% FIXME: remove export_all once the tests are active
-compile(export_all).
-compile(nowarn_export_all).

-spec check_ok_fun(string(), symtab:t(), ast:fun_decl(), ast:ty_scheme()) -> ok.
check_ok_fun(Filename, Tab, Decl = {function, L, Name, Arity, _}, Ty) ->
    Ctx = typing:new_ctx(Tab, error),
    try
        typing:check(Ctx, Decl, Ty)
    catch
        throw:{ety, ty_error, Msg} ->
            io:format("~s: Type checking ~w/~w in ~s failed but should succeed: ~s",
                      [ast:format_loc(L), Name, Arity, Filename, Msg]),
            ?assert(false)
    end,
    % FIXME: activate once the FIXME in typing:infer has been removed
    %[{_, InferredTy}] =
    %    try
    %        typing:infer([Decl], Tab)
    %    catch
    %        throw:{ety, ty_error, Msg2} ->
    %            io:format("~s: Type checking ~w/~w in ~s failed but should succeed: ~s",
    %                  [ast:format_loc(L), Name, Arity, Filename, Msg2]),
    %            ?assert(false)
    %    end,
    % FIXME: activate once more_general is working. This requires a working tally/3
    % case typing:more_general(InferredTy, Ty, Tab) of
    %     true -> ok;
    %     false ->
    %         io:format(
    %           "~s: Inferred type ~w for function ~w/~w in ~s is not more general than type ~w from spec",
    %           [ast:format_loc(L), InferredTy, Name, Arity, Filename, Ty]),
    %         ?assert(false)
    % end,
    ok.

-spec check_fail_fun(string(), symtab:t(), ast:fun_decl(), ast:ty_scheme()) -> ok.
check_fail_fun(Filename, Tab, Decl = {function, L, Name, Arity, _}, Ty) ->
    Ctx = typing:new_ctx(Tab, error),
    try
        typing:check(Ctx, Decl, Ty),
        io:format("~s: Type checking ~w/~w in ~s succeeded but should fail",
                  [ast:format_loc(L), Name, Arity, Filename]),
        ?assert(false)
    catch
        throw:{ety, ty_error, _Msg} ->
            ok
    end.

-type what() :: all | {include, sets:set(string())} | {exclude, sets:set(string())}.

-spec check_decls_in_file(string(), what()) -> ok.
check_decls_in_file(F, What) ->
  RawForms = parse:parse_file_or_die(F),
  Forms = ast_transform:trans(F, RawForms),
  Tab0 = symtab:std_symtab(),
  Tab = symtab:extend_symtab(Forms, Tab0),

  CollectDecls = fun(Decl, TestCases) ->
    case Decl of
      {function, Loc, Name, Arity, _} ->
        NameStr = atom_to_list(Name),
        case should_run(NameStr, What) of
          true ->
            TestCases ++ [
              {NameStr, fun() ->
                ?LOG_NOTE("Type checking ~s from ~s", NameStr, F),
                Ty = symtab:lookup_fun({ref, Name, Arity}, Loc, Tab),
                case utils:string_ends_with(NameStr, "_fail") of
                  true -> check_fail_fun(F, Tab, Decl, Ty);
                  false -> check_ok_fun(F, Tab, Decl, Ty)
                end
              end}
            ];
          false -> TestCases
        end;
      _ -> TestCases
    end
                 end,

  lists:foldl(CollectDecls, [], Forms).

-spec should_run(string(), what()) -> boolean().
should_run(_Name, all) -> true;
should_run(Name, {include,Set}) -> sets:is_element(Name, Set);
should_run(Name, {exclude,Set}) -> not sets:is_element(Name, Set).

simple_test_() ->
  WhatNot = [
    % FIXME #36 impossible branches bug, completeness bug
    "foo2",
    % TODO specials (float, pid, [], ...)
    "integer_07",
    "float_01",
    "float_02",
    "float_03",
    "float_04_fail",
    "float_05_fail",
    "case_09",
    % TODO lists
    "foo",
    "inter_04_fail",
    "nil_01",
    "nil_02",
    "nil_03",
    "nil_04",
    "nil_05_fail",
    "string_01",
    "string_02",
    "string_03",
    "string_04",
    "string_05_fail",
    "string_06_fail",
    "string_07",
    "string_08_fail",
    % TODO n-functions
    "fun_03",
    "fun_04_fail",
    "op_01",
    "op_02",
    "op_03",
    "op_04",
    "op_05",
    "op_06_fail",
    "op_07_fail",
    "op_08",
    "block_01",
    "block_02_fail",
    "block_03",
    "catch_01",
    "catch_02",
    "catch_03_fail",
    "cons_01",
    "cons_02",
    "cons_03",
    "cons_04_fail",
    "cons_05",
    "cons_06_fail",
    "fun_local_01",
    "fun_local_02",
    "fun_local_03",
    "fun_local_04",
    "fun_local_05_fail",
    "if_01",
    "if_02",
    "if_03_fail",
    "if_04_fail",
    "if_05",
    "fun_ref_01",
    "fun_ref_02_fail",
    "fun_ref_03_fail",
    "inter_03_fail"
            ],
  check_decls_in_file("test_files/tycheck_simple.erl",
                      {exclude, sets:from_list(WhatNot)}).
