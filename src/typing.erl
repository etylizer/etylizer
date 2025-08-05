-module(typing).

-export([
    check_forms/5,
    new_ctx/3
]).

-include("log.hrl").
-include("typing.hrl").

-spec new_ctx(symtab:t(), symtab:t(), t:opt(ast_check:ty_map())) -> ctx().
new_ctx(Tab, Overlay, Sanity) ->
    Ctx = #ctx{ symtab = Tab, overlay_symtab = Overlay, sanity = Sanity },
    Ctx.

% Checks all forms of a module
-spec check_forms(ctx(), string(), ast:forms(), sets:set(string()), sets:set(string())) -> ok.
check_forms(Ctx, FileName, Forms, Only, Ignore) ->
    ExtTab = symtab:extend_symtab(FileName, Forms, Ctx#ctx.symtab, Ctx#ctx.overlay_symtab),
    ExtCtx = Ctx#ctx { symtab = ExtTab },
    ?LOG_DEBUG("Only: ~200p", sets:to_list(Only)),
    ?LOG_DEBUG("Ignore: ~200p", sets:to_list(Ignore)),
    % Split in functions with and without tyspec
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
                    X = {QRefStr, RefStr, NameStr},
                    Check = should_check(QRefStr, RefStr, NameStr, Only, Ignore),
                    case symtab:find_fun(Ref, ExtTab) of
                        error ->
                            if
                              Check ->
                                  {With, [Form | Without], [X | Knowns]};
                              true ->
                                  errors:some_error(
                                      "~s: Cannot ignore function without type spec: ~s", [FileName, RefStr]
                                  )
                            end;
                        {ok, Ty} ->
                            if
                                Check -> {[{Form, Ty} | With], Without, [X | Knowns]};
                                true ->
                                    ?LOG_INFO("~s: not type checking function ~s as requested",
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
    {WithModuleName, WithArity, JustNames} = lists:unzip3(KnownFuns),
    Unknowns = sets:subtract(Only,
        sets:union([sets:from_list(WithModuleName, [{version, 2}]),
                        sets:from_list(WithArity, [{version, 2}]),
                        sets:from_list(JustNames, [{version, 2}])])),
    case sets:is_empty(Unknowns) of
        true -> ok;
        false ->
            ?LOG_INFO("Unknown functions in only: ~200p", sets:to_list(Unknowns))
    end,
    % infer types of functions without spec
    InferredTyEnvs = typing_infer:infer_all(ExtCtx, FileName, FunsWithoutSpec),
    % Typechecks the functions with a type spec. We need to check against all InferredTyEnvs,
    % we can stop on the first success.
    ?LOG_INFO("Checking ~w functions in ~s against their specs (~w environments)",
              length(FunsWithSpec), FileName, length(InferredTyEnvs)),
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
                        case typing_check:check_all(ExtCtx, FileName, E, FunsWithSpec) of
                            ok -> ok; % we are done
                            {error, Msg} -> Loop(RestEnvs, [{E, Msg} | Errs])
                        end
                end
        end,
    Loop(InferredTyEnvs, []),
    ?LOG_INFO("Checking ~w functions in ~s against their specs finished successfully",
              length(FunsWithSpec), FileName).

-spec should_check(string(), string(), string(), sets:set(string()), sets:set(string())) -> boolean().
should_check(QRefStr, RefStr, NameStr, Only, Ignore) ->
    case sets:is_empty(Only) of
        true ->
            not (sets:is_element(QRefStr, Ignore)
                    orelse sets:is_element(RefStr, Ignore)
                    orelse sets:is_element(NameStr, Ignore));
        false ->
            sets:is_element(QRefStr, Only)
                orelse sets:is_element(RefStr, Only)
                orelse sets:is_element(NameStr, Only)
    end.
