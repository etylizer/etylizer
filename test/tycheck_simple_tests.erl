-module(tycheck_simple_tests).

% Test setup for all functions in test_files/tycheck_simple.erl

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").
-include("etylizer_main.hrl").
-include("parse.hrl").
-include("typing.hrl").

-spec check_ok_fun(string(), symtab:t(), symtab:t(), sets:set({atom(), arity()}), sets:set({atom(), arity()}), ast:fun_decl(), ast:ty_scheme()) -> ok.
check_ok_fun(Filename, Tab, OverlayTab, DisableExhaustiveness, DisableRedundancy, Decl = {function, L, Name, Arity, _}, Ty) ->
    Includes = ["include", "src", "src/erlang_types", "src/erlang_types/dnf", "src/erlang_types/utils"],
    SanityCheck = cm_check:perform_sanity_check(Filename, [Decl], true, Includes),
    Ctx0 = typing:new_ctx(Tab, OverlayTab, SanityCheck), % FIXME: perform sanity check!
    Ctx = Ctx0#ctx{ disable_exhaustiveness = DisableExhaustiveness, disable_redundancy = DisableRedundancy },
    try
        typing_check:check(Ctx, Decl, Ty)
    catch
        throw:{etylizer, ty_error, Msg} ->
            io:format("~s: Type checking ~w/~w in ~s failed but should succeed: ~s",
                      [ast:format_loc(L), Name, Arity, Filename, Msg]),
            ?assert(false)
    end,
    ok.

-spec check_infer_ok_fun(string(), symtab:t(), symtab:t(), sets:set({atom(), arity()}), sets:set({atom(), arity()}), ast:fun_decl(), ast:ty_scheme()) -> ok.
check_infer_ok_fun(Filename, Tab, OverlayTab, DisableExhaustiveness, DisableRedundancy, Decl = {function, L, Name, Arity, _}, Ty) ->
    % Check that the inferred type is more general then the type in the spec
    Ctx0 = typing:new_ctx(Tab, OverlayTab, error),
    Ctx = Ctx0#ctx{ disable_exhaustiveness = DisableExhaustiveness, disable_redundancy = DisableRedundancy },
    Envs =
       try
           typing_infer:infer(Ctx, [Decl])
       catch
           throw:{etylizer, ty_error, Msg2} ->
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

-spec check_fail_fun(string(), symtab:t(), symtab:t(), sets:set({atom(), arity()}), sets:set({atom(), arity()}), ast:fun_decl(), ast:ty_scheme()) -> ok.
check_fail_fun(Filename, Tab, OverlayTab, DisableExhaustiveness, DisableRedundancy, Decl = {function, L, Name, Arity, _}, Ty) ->
    Ctx0 = typing:new_ctx(Tab, OverlayTab, error),
    Ctx = Ctx0#ctx{ disable_exhaustiveness = DisableExhaustiveness, disable_redundancy = DisableRedundancy },
    try
        typing_check:check(Ctx, Decl, Ty),
        io:format("~s: Type checking ~w/~w in ~s succeeded but should fail",
                  [ast:format_loc(L), Name, Arity, Filename]),
        ?assert(false)
    catch
        throw:{etylizer, ty_error, _Msg} ->
            ok
    end.

-type what() :: all | {include, sets:set(string())} | {exclude, sets:set(string())}.

-spec has_intersection(ast:ty_scheme()) -> boolean().
has_intersection({ty_scheme, _, {intersection, _}}) -> true;
has_intersection({ty_scheme, _, _}) -> false.

-spec check_decls_in_file(string(), what(), sets:set(string())) -> list().
check_decls_in_file(F, What, NoInfer) ->
  {ok, RawForms} = parse:parse_file(F, #parse_opts{includes =
                                                   ["include", "src", "src/erlang_types",
                                                    "src/erlang_types/dnf", "src/erlang_types/utils"]}),
  Forms = ast_transform:trans(F, RawForms),
  SearchPath = paths:compute_search_path(#opts{}),
  OverlayTab = symtab:empty(),
  Tab0 = symtab:std_symtab(SearchPath, symtab:empty()),
  Tab = symtab:extend_symtab(F, Forms, Tab0,symtab:empty()),
  DisableExhaustiveness = typing:resolve_disabled_funs(functions_exhaustive, Forms),
  DisableRedundancy = typing:resolve_disabled_funs(functions_redundant, Forms),

  CollectDecls = fun(Decl, TestCases) ->
    case Decl of
      {function, Loc, Name, Arity, _} ->
        NameStr = atom_to_list(Name),
        FullNameStr = F ++ "/" ++ atom_to_list(Name),
        Ty = symtab:lookup_fun({ref, Name, Arity}, Loc, Tab),
        ShouldFail = utils:string_ends_with(NameStr, "_fail"),
        RunTest =
          {timeout, 55, {FullNameStr ++ " (typecheck)", fun() ->
                ?LOG_NOTE("Type checking ~s from ~s", NameStr, F),
                global_state:with_new_state(fun() ->
                  case ShouldFail of
                    true -> check_fail_fun(F, Tab, OverlayTab, DisableExhaustiveness, DisableRedundancy, Decl, Ty);
                    false ->
                      check_ok_fun(F, Tab, OverlayTab, DisableExhaustiveness, DisableRedundancy, Decl, Ty)
                  end
                                            end)
              end}
            },
        InferTest =
          {timeout, 10, {FullNameStr ++ " (infer)", fun() ->
                ?LOG_NOTE("Infering type for ~s from ~s", NameStr, F),
                global_state:with_new_state(fun() ->
                  check_infer_ok_fun(F, Tab, OverlayTab, DisableExhaustiveness, DisableRedundancy, Decl, Ty)
                end),
                ok
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
  % FIXME #339
  NominalPart = [
    "different_nominal_01_fail",
    "different_nominal_02_fail",
    "tuple_different_01_fail",
    "chain_01_fail",
    "chain_03_fail",
    "chain_tuple_01_fail",
    "chain_tuple_02_fail",
    "chain_named_01_fail",
    "chain_mu_01_fail",
    "wrapper_02_fail",
    "wrapper_03_fail",
    "nested_01_fail",
    "union_downcast_01_fail",
    "union_chain_01_fail",
    "union_tuple_01_fail",
    "union_list_01_fail",
    "alias_unfold_01_fail",
    "alias_unfold_02_fail",
    "alias_unfold_04_fail",
    "alias_unfold_07_fail",
    "alias_unfold_08_fail",
    "map_01_fail",
    "map_03_fail",
    "cons_01_fail",
    "cons_04_fail",
    "contra_01_fail",
    "negation_01_fail",
    "nested_alias_2_fail",
    "nested_alias_3_fail",
    "nested_alias_4_fail",
    "nested_alias_both_fail",
    "inter_rhs_01_fail",
    "inter_rhs_03_fail",
    "inter_lhs_01_fail",
    "mu_01_fail"
  ],

  BinaryPart = [
    % slow
    "bin_match_float_01",
    % feature: project bits into integer values
    "bin_let_04"
  ],


  % The following functions are currently excluded from being tested.
  WhatNot = NominalPart ++
    BinaryPart ++ [
    % FIXME slow, waiting for optiization
    "refine_02",
    % TODO binary pattern element size verification
    "b4_fail",
    % TODO better redundancy check detection for dynamic()
    "refine_times_02_fail",
    "refine_times_03_fail",
    % TODO for if expressions guards always reference outer scope variables
    %      lower is always none() for any non-trivial if guard
    %      see case_13_fail, maybe at some point we have better
    %      bounds for scoped variables
    "if_06",
    "if_17",
    "if_18",
    "case_26",
    "refinement_01c",
    "refinement_01b"
  ],

  NoInfer = [
    % TODO slow, timeouts
    "guard_or_narrow_01",
    "dyn_union_case_02",
    "op_04",
    "op_15",
    "list_as_tuple_05",
    "refine_01",
    "refine_02",
    "refine_tagged_tuple",
    "refinement_string",
    "b3",
    "b5_embed_bitstring",
    "b5_embed_binary_unit1",
    "b5_embed_binary",
    "b5_match_binary_unit16_2bytes",
    "b5_match_binary_unit16_4bytes",
    "b5_truncate_binary",
    "bin_construct_int_02",
    "bin_construct_int_04",
    "bin_construct_int_05",
    "bin_construct_int_07",
    "bin_construct_int_08",
    "bin_construct_float_01",
    "bin_construct_float_02",
    "bin_construct_float_03",
    "bin_construct_str_01",
    "bin_construct_bin_03",
    "bin_construct_complex_01",
    "bin_construct_utf16_01",
    "bin_construct_utf16_02",
    "bin_construct_utf32_01",
    "bin_construct_fixed_01",
    "bin_construct_fixed_03",
    "bin_construct_match_int_01",
    "bin_match_int_01",
    "bin_match_int_02",
    "bin_match_int_03",
    "bin_match_int_04",
    "bin_match_int_05",
    "bin_match_int_06",
    "bin_match_int_07",
    "bin_exhaust_01",
    "bin_exhaust_03",
    "bin_exhaust_02",
    "bin_exhaust_04",
    "bin_match_bin_01",
    "bin_match_bin_02",
    "bin_match_bin_03",
    "bin_match_literal_01",
    "bin_match_literal_02",
    "bin_match_literal_03",
    "bin_match_float_02",
    "bin_concat_01",
    "bin_concat_02",
    "bin_concat_03",
    "bin_guard_01",
    "bin_guard_02",
    "bin_guard_04",
    "bin_guard_05",
    "bin_guard_literal_01",
    "bin_guard_literal_02",
    "bin_occ_02",
    "bin_precise_01",
    "bin_precise_02",
    "bin_precise_03",
    "bin_precise_04",
    "bin_comp_02",
    "bin_comp_03",
    "bin_comp_06",
    "bin_subtype_01",
    "bin_try_01",
    "bin_fun_01_helper",
    "bin_data_02",
    "bin_let_01",
    "bin_let_02",
    "bin_let_03",
    "bin_rec_01",
    "bin_rec_02",
    "bin_rec_03",
    "bin_rec_04",
    "bin_cons_01",
    "bin_cons_03",
    "bin_cons_04",
    "bin_bif_guard_01",
    "bin_bif_guard_02",
    "bin_case_01",
    "bin_case_02",
    "bin_concat_04",
    "bin_llet_04",
    "bin_utf8_cons_01",
    "bin_utf8_cons_03",
    "bin_utf8_cons_04",
    "bin_utf8_cons_05",
    "bin_utf8_cons_06",
    "b5_embed_1bit_bitstring",
    "b5_embed_1bit_binary_unit1",
    "b5_match_binary_unit16_empty",
    % TODO timeout, with flipped variable ordering it infers instantly
    "match_13",
    % TODO slow (tuple-encoded lists) inference #255
    % reason: recursive types parsing and unparsing in solving step (missing proper substitution implementation)
    "mu_03",
    "list_as_tuple_12",
    "list_as_tuple_rep_02",
    "list_as_tuple_08",
    "list_pattern_11",
    "list_pattern_10_fail_h",
    "list_pattern_02",
    "list_pattern_07",
    "inter_04_ok",
    "foo",
    "op_08",
    % TODO slow maybe inference
    "maybe_08",
    "maybe_09"
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
