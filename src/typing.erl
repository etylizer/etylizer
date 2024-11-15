-module(typing).

-export([
    check_forms/4,
    new_ctx/2
]).

-export_type([ctx/0]).

-include_lib("log.hrl").
-include_lib("typing.hrl").

-spec new_ctx(symtab:t(), t:opt(ast_check:ty_map())) -> ctx().
new_ctx(Tab, Sanity) ->
    Ctx = #ctx{ symtab = Tab, sanity = Sanity },
    Ctx.

% Checks all forms of a module
-spec check_forms(ctx(), string(), ast:forms(), sets:set(string())) -> ok.
check_forms(Ctx, FileName, Forms, Only) ->
    ExtTab = symtab:extend_symtab(FileName, Forms, Ctx#ctx.symtab),
    ExtCtx = Ctx#ctx { symtab = ExtTab },
    % Split in functions with and without tyspec
    {FunsWithSpec, FunsWithoutSpec, KnownFuns} =
        lists:foldr(
          fun(Form, Acc = {With, Without, Knowns}) ->
                  case Form of
                      {function, Loc, Name, Arity, _Clauses} ->
                          Ref = {ref, Name, Arity},
                          RefStr = utils:sformat("~w/~w", Name, Arity),
                          NameStr = utils:sformat("~w", Name),
                          X = {RefStr, NameStr},
                          case sets:is_empty(Only) orelse sets:is_element(RefStr, Only)
                              orelse sets:is_element(NameStr, Only) of
                              true ->
                                  case symtab:find_fun(Ref, ExtTab) of
                                      error -> {With, [Form | Without], [X | Knowns]};
                                      {ok, Ty} -> {[{Form, Ty} | With], Without, [X | Knowns]}
                                  end;
                              false ->
                                  ?LOG_DEBUG("~s: not type checking function ~s as requested",
                                             ast:format_loc(Loc), RefStr),
                                  {With, Without, [X | Knowns]}
                          end;
                      _ -> Acc
                  end
          end,
          {[], [], []},
          Forms
         ),
    % Make sure that Only does not contain an unknown function
    {WithArity, JustNames} = lists:unzip(KnownFuns),
    Unknowns = sets:subtract(Only, sets:union(sets:from_list(WithArity), sets:from_list(JustNames))),
    case sets:is_empty(Unknowns) of
        true -> ok;
        false ->
            ?LOG_WARN("Unknown functions in only: ~200p", sets:to_list(Unknowns))
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
