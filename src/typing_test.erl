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
    ok.

-spec check_infer_ok_fun(string(), symtab:t(), ast:fun_decl(), ast:ty_scheme()) -> ok.
check_infer_ok_fun(Filename, Tab, Decl = {function, L, Name, Arity, _}, Ty) ->
    % Check that the infered type is more general then the type in the spec
    Ctx = typing:new_ctx(Tab, error),
    Envs =
       try
           typing:infer(Ctx, [Decl])
       catch
           throw:{ety, ty_error, Msg2} ->
               io:format("~s: Type checking ~w/~w in ~s failed but should succeed: ~s",
                     [ast:format_loc(L), Name, Arity, Filename, Msg2]),
               ?assert(false)
       end,
    InferredTys =
      lists:map(
        fun(Env) ->
          case maps:to_list(Env) of
            [{_, T}] -> T;
            _ -> io:format("Type map with more than one entry", []),
                  ?assert(false)
          end
        end,
        Envs),
    ?LOG_NOTE("Inferred the following types for ~w/~w: ~s", Name, Arity,
      pretty:render_list(", ", InferredTys, fun pretty:tyscheme/1)),
    case lists:any(
            fun(InferredTy) -> typing:more_general(InferredTy, Ty, Tab) end,
            InferredTys)
      of
          true -> ok;
          false ->
              io:format(
                "~s: None of the inferred types ~s for function ~w/~w in ~s is more general than type ~s from spec",
                [ast:format_loc(L),
                pretty:render_list(", ", InferredTys, fun pretty:tyscheme/1),
                Name, Arity, Filename,
                pretty:render_tyscheme(Ty)]),
              ?assert(false)
      end,
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

-spec check_decls_in_file(string(), what(), sets:set(string())) -> ok.
check_decls_in_file(F, What, NoInfer) ->
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
                  false ->
                    check_ok_fun(F, Tab, Decl, Ty),
                    case sets:is_element(NameStr, NoInfer) of
                      true -> ok;
                      false -> check_infer_ok_fun(F, Tab, Decl, Ty)
                    end
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
             "fun_local_02" % TODO 4s
            , "fun_local_03" % TODO 10s
            , "fun_local_04" % TODO 6s
            , "foo2" % TODO very long
            , "foo3" % TODO very long
            ],
  NoInfer = [],
  %What = ["case_06"],
  check_decls_in_file("test_files/tycheck_simple.erl",
                      {exclude, sets:from_list(WhatNot)},
                      %{include, sets:from_list(What)},
                      sets:from_list(NoInfer)).
