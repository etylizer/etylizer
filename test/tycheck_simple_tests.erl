-module(tycheck_simple_tests).

% Test setup for all functions in test_files/tycheck_simple.erl

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").
-include("ety_main.hrl").

-spec check_ok_fun(string(), symtab:t(), ast:fun_decl(), ast:ty_scheme()) -> ok.
check_ok_fun(Filename, Tab, Decl = {function, L, Name, Arity, _}, Ty) ->
    SanityCheck = cm_check:perform_sanity_check(Filename, [Decl], true),
    Ctx = typing:new_ctx(Tab, SanityCheck), % FIXME: perform sanity check!
    try
        typing_check:check(Ctx, Decl, Ty)
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
           typing_infer:infer(Ctx, [Decl])
       catch
           throw:{ety, ty_error, Msg2} ->
               io:format("~s: Infering type for ~w/~w in ~s failed but should succeed: ~s",
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
      pretty:render_list(fun pretty:tyscheme/1, InferredTys)),
    case lists:any(
            fun(InferredTy) -> typing_infer:more_general(L, InferredTy, Ty, Tab) end,
            InferredTys)
      of
          true -> ok;
          false ->
              io:format(
                "~s: None of the inferred types ~s for function ~w/~w in ~s is more general than type ~s from spec",
                [ast:format_loc(L),
                pretty:render_list(fun pretty:tyscheme/1, InferredTys),
                Name, Arity, Filename,
                pretty:render_tyscheme(Ty)]),
              ?assert(false)
      end,
    ok.

-spec check_fail_fun(string(), symtab:t(), ast:fun_decl(), ast:ty_scheme()) -> ok.
check_fail_fun(Filename, Tab, Decl = {function, L, Name, Arity, _}, Ty) ->
    Ctx = typing:new_ctx(Tab, error),
    try
        typing_check:check(Ctx, Decl, Ty),
        io:format("~s: Type checking ~w/~w in ~s succeeded but should fail",
                  [ast:format_loc(L), Name, Arity, Filename]),
        ?assert(false)
    catch
        throw:{ety, ty_error, _Msg} ->
            ok
    end.

-type what() :: all | {include, sets:set(string())} | {exclude, sets:set(string())}.

-spec has_intersection(ast:ty_scheme()) -> boolean().
has_intersection({ty_scheme, _, {intersection, _}}) -> true;
has_intersection({ty_scheme, _, _}) -> false.

-spec check_decls_in_file(string(), what(), sets:set(string())) -> list().
check_decls_in_file(F, What, NoInfer) ->
  RawForms = parse:parse_file_or_die(F),
  Forms = ast_transform:trans(F, RawForms),
  SearchPath = paths:compute_search_path(#opts{}),
  Tab0 = symtab:std_symtab(SearchPath),
  Tab = symtab:extend_symtab(F, Forms, Tab0),

  CollectDecls = fun(Decl, TestCases) ->
    case Decl of
      {function, Loc, Name, Arity, _} ->
        NameStr = atom_to_list(Name),
        FullNameStr = F ++ "/" ++ atom_to_list(Name),
        Ty = symtab:lookup_fun({ref, Name, Arity}, Loc, Tab),
        ShouldFail = utils:string_ends_with(NameStr, "_fail"),
        RunTest =
          % FIXME #54 reduce timeout after issue has been fixed
          {timeout, 45, {FullNameStr, fun() ->
                ?LOG_NOTE("Type checking ~s from ~s", NameStr, F),
                test_utils:reset_ets(),
                case ShouldFail of
                  true -> check_fail_fun(F, Tab, Decl, Ty);
                  false ->
                    check_ok_fun(F, Tab, Decl, Ty)
                end
              end}
            },
        InferTest =
          {timeout, 45, {FullNameStr ++ " (infer)", fun() ->
                ?LOG_NOTE("Infering type for ~s from ~s", NameStr, F),
                test_utils:reset_ets(),
                check_infer_ok_fun(F, Tab, Decl, Ty)
              end}
          },
        ShouldRun = should_run(NameStr, What),
        ShouldInfer = not ShouldFail andalso not sets:is_element(NameStr, NoInfer)
          andalso not has_intersection(Ty),
        ExtraTestCases =
          case {ShouldRun, ShouldInfer} of
            {false, _} -> [];
            {true, true} -> [RunTest, InferTest];
            {true, false} -> [RunTest]
          end,
        TestCases ++ ExtraTestCases;
      _ -> TestCases
    end
  end,
  lists:foldl(CollectDecls, [], Forms).

%% Suppress warnings about unmatched patterns
%% TODO fix this somehow or not...
-dialyzer({no_match, should_run/2}).
-spec should_run(string(), all | {include, sets:set(string())} | {exclude, sets:set(string())}) -> boolean().
should_run(Name, {include, Set}) -> sets:is_element(Name, Set);
should_run(Name, {exclude, Set}) -> not sets:is_element(Name, Set);
should_run(_Name, all) -> true.



-spec check_decls_in_files(list(string()), what(), sets:set(string())) -> list().
check_decls_in_files(Files, What, NoInfer) ->
  CollectDecls = fun(File, TestCases) ->
    TestCases ++ check_decls_in_file(File, What, NoInfer)
  end,
  lists:foldl(CollectDecls, [], Files).

simple_test_() ->
  % The following functions are currently excluded from being tested.
  WhatNot = [
    % Redundancy check for lists is not powerful enough, see #108
    "list_pattern_08_fail",
    % #115 slow
    "user_07"
  ],

  NoInfer = [
    % slow, see #62
    "foo3",
    % TODO recursive inference
    "user_06", "user_07",
    % TODO see #164
    "match_13"
  ],

  %What = ["atom_03_fail"],
  TopDir = "test_files/tycheck_simple",

  % If OnlyFiles is empty, all files not in IgnoreFiles are checked
  % If OnlyFiles is not empty, only the files in OnlyFiles but not in IgnoreFiels are checked
  OnlyFiles = [],
  IgnoreFiles = [],

  parse_cache:with_cache(
    #opts{},
    fun() ->
      case file:list_dir(TopDir) of
        {ok, Entries} ->
            ErlFiles =
              lists:filtermap(fun(Entry) ->
                case filename:extension(Entry) =:= ".erl" andalso
                  (OnlyFiles =:= [] orelse lists:member(Entry, OnlyFiles)) andalso
                  (not lists:member(Entry, IgnoreFiles))
                of
                  true -> {true, TopDir ++ "/" ++ Entry};
                  false -> false
                end
              end, Entries),
            case ErlFiles of
              [] -> erlang:error("No test files found in " ++ TopDir);
              _ -> ok
            end,
            check_decls_in_files(ErlFiles,
                          {exclude, sets:from_list(WhatNot)},
                          %{include, sets:from_list(What)},
                          sets:from_list(NoInfer));
        _ -> erlang:error("Failed to list test directory " ++ TopDir)
      end
    end).
