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
%    % Check that the inffered type is more general then the type in the spec
%    Envs =
%       try
%           typing:infer(Ctx, [Decl])
%       catch
%           throw:{ety, ty_error, Msg2} ->
%               io:format("~s: Type checking ~w/~w in ~s failed but should succeed: ~s",
%                     [ast:format_loc(L), Name, Arity, Filename, Msg2]),
%               ?assert(false)
%       end,
%    InferredTy =
%        case Envs of
%            [Env] ->
%                case maps:to_list(Env) of
%                    [{_, T}] -> T;
%                    _ -> io:format("Type map with more than one entry", []),
%                         ?assert(false)
%                end;
%            L -> io:format("List of maps with ~w elements", [length(L)]),
%                 ?assert(false)
%        end,
%    case typing:more_general(InferredTy, Ty, Tab) of
%        true -> ok;
%        false ->
%            io:format(
%              "~s: Inferred type ~w for function ~w/~w in ~s is not more general than type ~w from spec",
%              [ast:format_loc(L), InferredTy, Name, Arity, Filename, Ty]),
%            ?assert(false)
%    end,
%    ok.

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
              % FIXME #54 reduce timeout after issue has been fixed
              {timeout, 45, {NameStr, fun() ->
                ?LOG_NOTE("Type checking ~s from ~s", NameStr, F),
                test_utils:reset_ets(),
                Ty = symtab:lookup_fun({ref, Name, Arity}, Loc, Tab),
                case utils:string_ends_with(NameStr, "_fail") of
                  true -> check_fail_fun(F, Tab, Decl, Ty);
                  false -> check_ok_fun(F, Tab, Decl, Ty)
                end
              end}}
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
    % FIXME #36 impossible branches
    "foo2",
    "inter_03_fail",
    % FIXME #61 bad recursive types in tally
    "tuple_04",
    % slow, see #57
    "list_pattern_02",
    "list_pattern_07",
    "some_fun",
    "fun_local_03",
    "fun_local_04"
  ],
  check_decls_in_file("test_files/tycheck_simple.erl",
                      {exclude, sets:from_list(WhatNot)}).
