-module(typing).

-export([
    check_forms/6, check_forms/7,
    new_ctx/3,
    new_ctx/7,
    resolve_disabled_funs/2
]).

-include("log.hrl").
-include("typing.hrl").

-spec new_ctx(symtab:t(), symtab:t(), t:opt(ast_check:ty_map())) -> ctx().
new_ctx(Tab, Overlay, Sanity) ->
    new_ctx(Tab, Overlay, Sanity, early_exit, 5000, enabled, dynamic).

-spec new_ctx(symtab:t(), symtab:t(), t:opt(ast_check:ty_map()), feature_flags:report_mode(), pos_integer(), feature_flags:exhaustiveness_mode(), feature_flags:gradual_typing_mode()) -> ctx().
new_ctx(Tab, Overlay, Sanity, ReportMode, ReportTimeout, ExhaustivenessMode, GradualTypingMode) ->
    Ctx = #ctx{ symtab = Tab, overlay_symtab = Overlay, sanity = Sanity, gradual_typing_mode = GradualTypingMode, report_mode = ReportMode, report_timeout = ReportTimeout, exhaustiveness_mode = ExhaustivenessMode },
    Ctx.

% Resolves the set of functions for which a feature is disabled from forms.
% Parses -etylizer({Feature, off}) for module-level and
% -etylizer({Feature, off, [fun/arity]}) for function-level.
-spec resolve_disabled_funs(atom(), ast:forms()) -> sets:set({atom(), arity()}).
resolve_disabled_funs(Feature, Forms) ->
    {ModuleOff, PerFunOff} = lists:foldl(
      fun(Form, {MO, PF}) ->
          case Form of
              {attribute, _, etylizer, {F, off}} when F =:= Feature ->
                  {true, PF};
              {attribute, _, etylizer, {F, off, Funs}} when F =:= Feature ->
                  {MO, sets:union(PF, sets:from_list(Funs))};
              _ -> {MO, PF}
          end
      end,
      {false, sets:new()},
      Forms),
    case ModuleOff of
        true ->
            % Module-level off: all functions are disabled
            lists:foldl(
                fun(Form, Acc) ->
                    case Form of
                        {function, _, Name, Arity, _} -> sets:add_element({Name, Arity}, Acc);
                        _ -> Acc
                    end
                end, sets:new(), Forms);
        false ->
            PerFunOff
    end.

% Checks all forms of a module
-spec check_forms(ctx(), string(), ast:forms(), sets:set(string()), sets:set(string()), boolean()) -> [{atom(), arity()}].
check_forms(Ctx, FileName, Forms, Only, Ignore, CheckExports) ->
    check_forms(Ctx, FileName, Forms, Only, Ignore, CheckExports, {sets:new(), sets:new()}).

-spec check_forms(ctx(), string(), ast:forms(), sets:set(string()), sets:set(string()), boolean(), {sets:set({atom(), arity()}), sets:set({atom(), arity()})}) -> [{atom(), arity()}].
check_forms(Ctx, FileName, Forms, Only, Ignore, CheckExports, {CliNoExhaustiveness, CliNoRedundancy}) ->
    case CheckExports orelse Ctx#ctx.gradual_typing_mode =:= infer of
        true ->
            ?LOG_DEBUG("Checking whether exported functions in ~s have a type spec", FileName),
            check_exported_funs_specified(Forms);
        false ->
            ?LOG_DEBUG("Skipping check for exported functions in ~s", FileName)
    end,
    ExtTab = symtab:extend_symtab(FileName, Forms, Ctx#ctx.symtab, Ctx#ctx.overlay_symtab),
    DisableExhaustiveness = sets:union(resolve_disabled_funs(functions_exhaustive, Forms), CliNoExhaustiveness),
    DisableRedundancy = sets:union(resolve_disabled_funs(functions_redundant, Forms), CliNoRedundancy),
    ExtCtx = Ctx#ctx { symtab = ExtTab, disable_exhaustiveness = DisableExhaustiveness, disable_redundancy = DisableRedundancy },
    ?LOG_DEBUG("Only: ~200p", sets:to_list(Only)),
    ?LOG_DEBUG("Ignore: ~200p", sets:to_list(Ignore)),
    % Split in functions with and without tyspec
    GradualMode = ExtCtx#ctx.gradual_typing_mode,
    {FunsWithSpec, FunsWithoutSpec, KnownFuns} =
        lists:foldr(
          fun(Form, Acc = {With, Without, Knowns}) ->
            case Form of
                {function, Loc, Name, Arity, _Clauses} ->
                    ModuleName = ast_utils:modname_from_path(FileName),
                    Ref = {ref, Name, Arity},
                    RefStr = utils:sformat("~w/~w", Name, Arity),
                    QRefStr = utils:sformat("~w:~s", ModuleName, RefStr),
                    NameStr = utils:sformat("~w", Name),
                    ModStr = utils:sformat("~w", ModuleName),
                    X = {QRefStr, RefStr, NameStr, ModStr},
                    Check = should_check(QRefStr, RefStr, NameStr, ModStr, Only, Ignore),
                    case symtab:find_fun(Ref, ExtTab) of
                        error ->
                            if
                              Check ->
                                  case GradualMode of
                                      dynamic ->
                                          DynTy = dynamic_ty_scheme(Arity),
                                          {[{Form, DynTy} | With], Without, [X | Knowns]};
                                      infer ->
                                          {With, [Form | Without], [X | Knowns]}
                                  end;
                              true ->
                                  case GradualMode of
                                      dynamic ->
                                          {With, Without, [X | Knowns]};
                                      infer ->
                                          errors:some_error(
                                              "~s: Cannot ignore function without type spec: ~s", [FileName, RefStr]
                                          )
                                  end
                            end;
                        {ok, Ty} ->
                            if
                                Check -> {[{Form, Ty} | With], Without, [X | Knowns]};
                                true ->
                                    ?LOG_TRACE("~s: not type checking function ~s as requested",
                                               ast:format_loc(Loc), RefStr),
                                    {With, Without, [X | Knowns]}
                            end
                    end;
                _ -> Acc
            end
          end,
          {[], [], []},
          Forms
         ),
    % Make sure that Only does not contain an unknown function
    AllKnown = lists:flatmap(fun({QRef, Ref, N, M}) -> [QRef, Ref, N, M] end, KnownFuns),
    Unknowns = sets:subtract(Only, sets:from_list(AllKnown, [{version, 2}])),
    case sets:is_empty(Unknowns) of
        true -> ok;
        false ->
            ?LOG_INFO("Unknown functions in only: ~200p", sets:to_list(Unknowns))
    end,
    % Infer types of functions without spec (empty in dynamic mode)
    InferredTyEnvs = typing_infer:infer_all(ExtCtx, FileName, FunsWithoutSpec),
    % Typechecks the functions with a type spec. We need to check against all InferredTyEnvs,
    % we can stop on the first success.
    ?LOG_DEBUG("Checking ~w functions in ~s against their specs (~w environments)",
              length(FunsWithSpec), FileName, length(InferredTyEnvs)),

    % if in report mode, continue type checking
    ReportMode = Ctx#ctx.report_mode,
    Loop =
        fun Loop(Envs, Errs) ->
                case Envs of
                    [] ->
                        case Errs of
                            [] -> errors:bug("Lists of errors empty");
                            [{_, Msg}] -> errors:ty_error(Msg);
                            _ ->
                                Formatted =
                                    utils:map_flip(
                                      Errs,
                                      fun({Env, Msg}) ->
                                              utils:sformat("~s:\nEnv: ~s",
                                                            Msg,
                                                            pretty:render_fun_env(Env))
                                      end
                                     ),
                                Msg = utils:sformat("Checking functions against their specs " ++
                                                        "failed for all ~w type environments " ++
                                                        "inferred from functions without " ++
                                                        "specs.\n\n~s",
                                                    length(Errs), string:join(Formatted, "\n\n")),
                                errors:ty_error(Msg)
                        end;
                    [E | RestEnvs] ->
                        case ReportMode of
                            early_exit ->
                                case typing_check:check_all(ExtCtx, FileName, E, FunsWithSpec) of
                                    ok -> []; % we are done
                                    {error, Msg} -> Loop(RestEnvs, [{E, Msg} | Errs])
                                end;
                            report ->
                                typing_check:check_all_report(ExtCtx, FileName, E, FunsWithSpec)
                        end
                end
        end,
    FailedFuns = Loop(InferredTyEnvs, []),
    ?LOG_INFO("Checking ~w functions in ~s against their specs finished successfully",
              length(FunsWithSpec), FileName),
    FailedFuns.

-spec should_check(string(), string(), string(), string(), sets:set(string()), sets:set(string())) -> boolean().
should_check(QRefStr, RefStr, NameStr, ModStr, Only, Ignore) ->
    case sets:is_empty(Only) of
        true ->
            not (sets:is_element(QRefStr, Ignore)
                    orelse sets:is_element(RefStr, Ignore)
                    orelse sets:is_element(NameStr, Ignore)
                    orelse sets:is_element(ModStr, Ignore));
        false ->
            sets:is_element(QRefStr, Only)
                orelse sets:is_element(RefStr, Only)
                orelse sets:is_element(NameStr, Only)
                orelse sets:is_element(ModStr, Only)
    end.

% Creates a dynamic type scheme for a function with the given arity.
-spec dynamic_ty_scheme(non_neg_integer()) -> ast:ty_scheme().
dynamic_ty_scheme(Arity) ->
    DynamicArgs = lists:duplicate(Arity, {predef, dynamic}),
    {ty_scheme, [], {fun_full, DynamicArgs, {predef, dynamic}}}.

-spec check_exported_funs_specified(ast:forms()) -> ok | no_return().
check_exported_funs_specified(Forms) ->
    Exported = [Exp || {attribute, _, export, Exports} <- Forms, Exp <- Exports],
    Speced = [{Fun, Arity} || {attribute, _, spec, Fun, Arity, _, _} <- Forms],
    Missing = [ utils:sformat("~w/~w", Fun, Arity) || {Fun, Arity} <- Exported, not lists:member({Fun, Arity}, Speced) ],
    case Missing of
        [] -> ok;
    _ ->
        errors:ty_error(utils:sformat("The following exported functions have no type specification: ~s", [string:join(Missing, ", ")]))
    end.
