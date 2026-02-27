-module(typing).

-export([
    check_forms/6,
    new_ctx/3,
    new_ctx/7,
    new_ctx/8,
    disable_exhaustiveness_from_forms/1
]).

-include("log.hrl").
-include("typing.hrl").
-include("etylizer.hrl").

-spec new_ctx(symtab:t(), symtab:t(), t:opt(ast_check:ty_map())) -> ctx().
new_ctx(Tab, Overlay, Sanity) ->
    new_ctx(Tab, Overlay, Sanity, early_exit, 5000, enabled, dynamic).

-spec new_ctx(symtab:t(), symtab:t(), t:opt(ast_check:ty_map()), feature_flags:report_mode(), pos_integer(), feature_flags:exhaustiveness_mode(), feature_flags:gradual_typing_mode()) -> ctx().
new_ctx(Tab, Overlay, Sanity, ReportMode, ReportTimeout, ExhaustivenessMode, GradualTypingMode) ->
    new_ctx(Tab, Overlay, Sanity, ReportMode, ReportTimeout, ExhaustivenessMode, GradualTypingMode, false).

-spec new_ctx(symtab:t(), symtab:t(), t:opt(ast_check:ty_map()), feature_flags:report_mode(), pos_integer(), feature_flags:exhaustiveness_mode(), feature_flags:gradual_typing_mode(), boolean()) -> ctx().
new_ctx(Tab, Overlay, Sanity, ReportMode, ReportTimeout, ExhaustivenessMode, GradualTypingMode, SanityInfer) ->
    Ctx = #ctx{ symtab = Tab, overlay_symtab = Overlay, sanity = Sanity, gradual_typing_mode = GradualTypingMode, report_mode = ReportMode, report_timeout = ReportTimeout, exhaustiveness_mode = ExhaustivenessMode, sanity_infer = SanityInfer },
    Ctx.

% extracts the set of functions with disabled exhaustiveness from forms.
-spec disable_exhaustiveness_from_forms(ast:forms()) -> sets:set({atom(), arity()}).
disable_exhaustiveness_from_forms(Forms) ->
    lists:foldl(
      fun(Form, Acc) ->
          case Form of
              {attribute, _, etylizer, {disable_exhaustiveness, ListOfFuns}} ->
                  sets:union(Acc, sets:from_list(ListOfFuns));
              _ -> Acc
          end
      end,
      sets:new(),
      Forms).

% Checks all forms of a module. Returns the list of functions that failed
% type checking (empty in early-exit mode, since it throws on error).
-spec check_forms(ctx(), string(), ast:forms(), sets:set(string()), sets:set(string()), boolean()) -> [{atom(), arity()}].
check_forms(Ctx, FileName, Forms, Only, Ignore, CheckExports) ->
    case CheckExports orelse Ctx#ctx.gradual_typing_mode =:= infer of
        true ->
            ?LOG_DEBUG("Checking whether exported functions in ~s have a type spec", FileName),
            check_exported_funs_specified(Forms);
        false ->
            ?LOG_DEBUG("Skipping check for exported functions in ~s", FileName)
    end,
    ExtCtx = make_ext_ctx(Ctx, FileName, Forms),
    check_forms_classify(Ctx, ExtCtx, FileName, Forms, Only, Ignore).

-spec make_ext_ctx(ctx(), string(), ast:forms()) -> ctx().
make_ext_ctx(Ctx, FileName, Forms) ->
    ExtTab = symtab:extend_symtab(FileName, Forms, Ctx#ctx.symtab, Ctx#ctx.overlay_symtab),
    DisableExhaustiveness = disable_exhaustiveness_from_forms(Forms),
    Ctx#ctx { symtab = ExtTab, disable_exhaustiveness = DisableExhaustiveness }.

-spec check_forms_classify(ctx(), ctx(), string(), ast:forms(), sets:set(string()), sets:set(string())) -> [{atom(), arity()}].
check_forms_classify(Ctx, ExtCtx, FileName, Forms, Only, Ignore) ->
    ?LOG_DEBUG("Only: ~200p", sets:to_list(Only)),
    ?LOG_DEBUG("Ignore: ~200p", sets:to_list(Ignore)),
    {FunsWithSpec, FunsWithoutSpec, KnownFuns} =
        classify_forms(Forms, FileName, ExtCtx#ctx.symtab, ExtCtx#ctx.gradual_typing_mode, Only, Ignore),
    check_unknowns(Only, KnownFuns),
    check_forms_typecheck(Ctx, ExtCtx, FileName, FunsWithSpec, FunsWithoutSpec).

-spec check_forms_typecheck(ctx(), ctx(), string(), [{ast:fun_decl(), ast:ty_scheme()}], [ast:fun_decl()]) -> [{atom(), arity()}].
check_forms_typecheck(Ctx, ExtCtx, FileName, FunsWithSpec, FunsWithoutSpec) ->
    % Infer types of functions without spec (empty in dynamic mode)
    InferredTyEnvs = typing_infer:infer_all(ExtCtx, FileName, FunsWithoutSpec),
    ?LOG_DEBUG("Checking ~w functions in ~s against their specs (~w environments)",
              length(FunsWithSpec), FileName, length(InferredTyEnvs)),
    FailedFuns = check_against_envs(Ctx#ctx.report_mode, ExtCtx, FileName, FunsWithSpec, InferredTyEnvs, []),
    ?LOG_INFO("Checking ~w functions in ~s against their specs finished",
              length(FunsWithSpec), FileName),
    sanity_infer_check(ExtCtx, FileName, FunsWithSpec),
    FailedFuns.

-type classify_acc() :: {
    [{ast:fun_decl(), ast:ty_scheme()}],
    [ast:fun_decl()],
    [{string(), string(), string(), string()}]
}.

-spec classify_forms(ast:forms(), string(), symtab:t(), feature_flags:gradual_typing_mode(), sets:set(string()), sets:set(string())) -> classify_acc().
classify_forms(Forms, FileName, ExtTab, GradualMode, Only, Ignore) ->
    FunDecls = [F || F = {function, _, _, _, _} <- Forms],
    lists:foldr(
        fun(Form, Acc) -> classify_fun_decl(Form, Acc, FileName, ExtTab, GradualMode, Only, Ignore) end,
        {[], [], []},
        FunDecls).

-spec classify_fun_decl(ast:fun_decl(), classify_acc(), string(), symtab:t(), feature_flags:gradual_typing_mode(), sets:set(string()), sets:set(string())) -> classify_acc().
classify_fun_decl(Form = {function, Loc, Name, Arity, _Clauses}, Acc, FileName, ExtTab, GradualMode, Only, Ignore) ->
    ModName = ast_utils:modname_from_path(FileName),
    RefStr = utils:sformat("~w/~w", Name, Arity),
    QRefStr = utils:sformat("~w:~s", ModName, RefStr),
    NameStr = utils:sformat("~w", Name),
    ModStr = utils:sformat("~w", ModName),
    X = {QRefStr, RefStr, NameStr, ModStr},
    Check = should_check(QRefStr, RefStr, NameStr, ModStr, Only, Ignore),
    case symtab:find_fun({ref, Name, Arity}, ExtTab) of
        error ->
            case Check of
                true -> classify_no_spec_checked(Form, Arity, GradualMode, Acc, X);
                false -> classify_no_spec_ignored(FileName, RefStr, GradualMode, Acc, X)
            end;
        {ok, Ty} ->
            classify_with_spec(Check, Form, Loc, RefStr, Ty, Acc, X)
    end.

-spec classify_no_spec_checked(
    ast:fun_decl(), arity(), feature_flags:gradual_typing_mode(), classify_acc(),
    {string(), string(), string(), string()}) -> classify_acc().
classify_no_spec_checked(Form, Arity, dynamic, {With, Without, Knowns}, X) ->
    {[{Form, dynamic_ty_scheme(?assert_type(Arity, non_neg_integer()))} | With], Without, [X | Knowns]};
classify_no_spec_checked(Form, _Arity, infer, {With, Without, Knowns}, X) ->
    {With, [Form | Without], [X | Knowns]}.

-spec classify_no_spec_ignored(
    string(), string(), feature_flags:gradual_typing_mode(), classify_acc(),
    {string(), string(), string(), string()}) -> classify_acc().
classify_no_spec_ignored(_FileName, _RefStr, dynamic, {With, Without, Knowns}, X) ->
    {With, Without, [X | Knowns]};
classify_no_spec_ignored(FileName, RefStr, infer, _Acc, _X) ->
    errors:some_error("~s: Cannot ignore function without type spec: ~s", [FileName, RefStr]).

-spec classify_with_spec(
    boolean(), ast:fun_decl(), ast:loc(), string(), ast:ty_scheme(),
    classify_acc(), {string(), string(), string(), string()}) -> classify_acc().
classify_with_spec(true, Form, _Loc, _RefStr, Ty, {With, Without, Knowns}, X) ->
    {[{Form, Ty} | With], Without, [X | Knowns]};
classify_with_spec(false, _Form, Loc, RefStr, _Ty, {With, Without, Knowns}, X) ->
    ?LOG_TRACE("~s: not type checking function ~s as requested",
               ast:format_loc(Loc), RefStr),
    {With, Without, [X | Knowns]}.

-spec check_unknowns(sets:set(string()), [{string(), string(), string(), string()}]) -> ok.
check_unknowns(Only, KnownFuns) ->
    Known = lists:foldl(fun({QRef, Ref, Name, Mod}, Acc) ->
        [QRef, Ref, Name, Mod | Acc]
    end, [], KnownFuns),
    Unknowns = sets:subtract(Only, sets:from_list(Known, [{version, 2}])),
    case sets:is_empty(Unknowns) of
        true -> ok;
        false ->
            ?LOG_INFO("Unknown functions in only: ~200p", sets:to_list(Unknowns))
    end.

-spec check_against_envs(
    feature_flags:report_mode(), ctx(), string(),
    [{ast:fun_decl(), ast:ty_scheme()}], [symtab:fun_env()],
    [{symtab:fun_env(), string()}]) -> [{atom(), arity()}].
check_against_envs(_ReportMode, _ExtCtx, _FileName, _FunsWithSpec, [], Errs) ->
    case Errs of
        [] -> errors:bug("Lists of errors empty");
        [{_, Msg}] -> errors:ty_error(Msg);
        _ ->
            Formatted = lists:map(fun format_env_error/1, Errs),
            Msg = utils:sformat("Checking functions against their specs " ++
                                    "failed for all ~w type environments " ++
                                    "inferred from functions without " ++
                                    "specs.\n\n~s",
                                length(Errs), string:join(Formatted, "\n\n")),
            errors:ty_error(Msg)
    end;
check_against_envs(ReportMode, ExtCtx, FileName, FunsWithSpec, [E | RestEnvs], Errs) ->
    case ReportMode of
        early_exit ->
            case typing_check:check_all(ExtCtx, FileName, E, FunsWithSpec) of
                ok -> [];
                {error, Msg} ->
                    check_against_envs(ReportMode, ExtCtx, FileName, FunsWithSpec, RestEnvs, [{E, Msg} | Errs])
            end;
        report ->
            typing_check:check_all_report(ExtCtx, FileName, E, FunsWithSpec)
    end.

-spec format_env_error({symtab:fun_env(), string()}) -> string().
format_env_error({Env, Msg}) ->
    utils:sformat("~s:\nEnv: ~s", Msg, pretty:render_fun_env(Env)).

-spec sanity_infer_check(ctx(), string(), [{ast:fun_decl(), ast:ty_scheme()}]) -> ok.
sanity_infer_check(ExtCtx, FileName, FunsWithSpec) ->
    case ExtCtx#ctx.sanity_infer of
        true ->
            InferCtx = ExtCtx#ctx{sanity = error},
            lists:foreach(
                fun({Decl, SpecTy}) ->
                    sanity_infer_one(ExtCtx, InferCtx, FileName, Decl, SpecTy)
                end,
                FunsWithSpec);
        false -> ok
    end.

-spec sanity_infer_one(ctx(), ctx(), string(), ast:fun_decl(), ast:ty_scheme()) -> ok.
sanity_infer_one(ExtCtx, InferCtx, FileName, Decl = {function, _Loc, Name, Arity, _}, SpecTy) ->
    FunStr = utils:sformat("~w/~w", Name, Arity),
    ?LOG_INFO("Sanity inference check for ~s in ~s", FunStr, FileName),
    ?assert_type(global_state:with_new_state(fun() ->
        sanity_infer_one_inner(ExtCtx, InferCtx, FileName, Decl, SpecTy, FunStr)
    end), ok).

-spec sanity_infer_one_inner(ctx(), ctx(), string(), ast:fun_decl(), ast:ty_scheme(), string()) -> ok.
sanity_infer_one_inner(ExtCtx, InferCtx, FileName, Decl = {function, Loc, _Name, _Arity, _}, SpecTy, FunStr) ->
    % TODO disabling caching leads to different results for inference!
    Envs = typing_infer:infer_all(InferCtx, FileName, [Decl]),
    InferredTys = extract_inferred_tys(Envs),
    case lists:any(
            fun(InferredTy) ->
                typing_infer:more_general(Loc, InferredTy, SpecTy, ExtCtx#ctx.symtab)
            end,
            InferredTys)
    of
        true ->
            ?LOG_INFO("Sanity inference check passed for ~s", FunStr);
        false ->
            errors:ty_error(Loc,
                "Sanity inference check failed for ~s: "
                "no inferred type is more general than the spec",
                FunStr)
    end.

-spec extract_inferred_tys([symtab:fun_env()]) -> [ast:ty_scheme()].
extract_inferred_tys(Envs) ->
    lists:flatmap(fun(Env) -> [T || {_, T} <- maps:to_list(Env)] end, Envs).

-spec should_check(string(), string(), string(), string(), sets:set(string()), sets:set(string())) -> boolean().
should_check(QRefStr, RefStr, NameStr, ModStr, Only, Ignore) ->
    IsIgnored = sets:is_element(QRefStr, Ignore)
        orelse sets:is_element(RefStr, Ignore)
        orelse sets:is_element(NameStr, Ignore)
        orelse sets:is_element(ModStr, Ignore),
    case IsIgnored of
        true -> false;
        false ->
            case sets:is_empty(Only) of
                true -> true;
                false ->
                    sets:is_element(QRefStr, Only)
                        orelse sets:is_element(RefStr, Only)
                        orelse sets:is_element(NameStr, Only)
                        orelse sets:is_element(ModStr, Only)
            end
    end.

% Creates a dynamic type scheme for a function with the given arity.
-spec dynamic_ty_scheme(non_neg_integer()) -> ast:ty_scheme().
dynamic_ty_scheme(Arity) ->
    DynamicArgs = lists:duplicate(Arity, {predef, dynamic}),
    {ty_scheme, [], {fun_full, DynamicArgs, {predef, dynamic}}}.

-spec check_exported_funs_specified(ast:forms()) -> ok | no_return().
check_exported_funs_specified(Forms) ->
    Exported = lists:append([Exports || {attribute, _, export, Exports} <- Forms]),
    Speced = [{Fun, Arity} || {attribute, _, spec, Fun, Arity, _, _} <- Forms],
    Missing = [ utils:sformat("~w/~w", Fun, Arity) || {Fun, Arity} <- Exported, not lists:member({Fun, Arity}, Speced) ],
    case Missing of
        [] -> ok;
    _ ->
        errors:ty_error(utils:sformat("The following exported functions have no type specification: ~s", [string:join(Missing, ", ")]))
    end.
