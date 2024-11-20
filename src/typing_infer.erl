-module(typing_infer).

-export([
    infer_all/3,
    infer/2,
    more_general/4
]).

-include("log.hrl").
-include("typing.hrl").

% Infers the types of all the given functions.
-spec infer_all(ctx(), string(), [ast:fun_decl()]) -> [symtab:fun_env()].
infer_all(_Ctx, _FileName, []) -> [#{}];
infer_all(Ctx, FileName, Decls) ->
    ?LOG_INFO("Inferring types of functions without specs in ~s", FileName),
    % FIXME: need to build strongly connected components to infer each group in isolation
    L = infer(Ctx, Decls),
    ?LOG_INFO("Inferring types of functions without specs returned ~w environments in total",
              length(L)),
    L.

% Infers the types of a group of (mutually recursive) functions.
% For reasons of non-determinism, return a list of possible type
% environments for these functions.
% Throws a ty_error if no such environment exist.
-spec infer(ctx(), [ast:fun_decl()]) -> [symtab:fun_env()].
infer(_, []) -> errors:bug("typing_infer:infer called with empty list of declarations");
infer(Ctx, Decls) ->
    Funs = lists:map(fun ast:get_fun_name/1, Decls),
    FunsStr = string:join(Funs, ", "),
    ?LOG_INFO("Inferring types of the following functions: ~s", FunsStr),
    Loc =
        case Decls of
            [{function, L, _, _, _} | _] -> L
        end,
    {Cs, Env} = constr_gen:gen_constrs_fun_group(Ctx#ctx.symtab, Decls),
    case Ctx#ctx.sanity of
        {ok, TyMap} -> constr_gen:sanity_check(Cs, TyMap);
        error -> ok
    end,
    ?LOG_DEBUG("Constraints:~n~s", pretty:render_constr(Cs)),
    PolyEnv = maps:map(fun(_Key, T) -> {ty_scheme, [], T} end, Env),
    Tab = Ctx#ctx.symtab,
    SimpCtx = constr_simp:new_ctx(Tab, PolyEnv, Ctx#ctx.sanity),
    Funs =
        lists:map(
            fun({function, _Loc, Name, Arity, _}) ->
                    utils:sformat("~w/~w", Name, Arity)
            end,
            Decls),

    SimpConstrs = constr_simp:simp_constrs(SimpCtx, Cs),
    case Ctx#ctx.sanity of
        {ok, TyMap2} -> constr_simp:sanity_check(SimpConstrs, TyMap2);
        error -> ok
    end,
    FunNamesStr = string:join(Funs, ","),
    ?LOG_DEBUG("Simplified constraint set for a group of mutually recursive functions ~s, now " ++
                "checking constraints for solvability.~nConstraints:~n~s",
                FunNamesStr, pretty:render_constr(SimpConstrs)),
    SolveRes = constr_solve:solve_simp_constrs(Tab, SimpConstrs, "inference"),
    ResultEnvs =
        case SolveRes of
            error -> [];
            Substs ->
                utils:map_flip(Substs,
                    fun(Subst) ->
                            ResultEnv = maps:from_list(utils:map_flip(
                                Decls,
                                fun({function, _Loc, Name, Arity, _}) ->
                                        Ref = {ref, Name, Arity},
                                        case maps:find(Ref, Env) of
                                            error ->
                                                errors:bug("Function ~w/~w not found in env",
                                                            [Name, Arity]);
                                            {ok, T} ->
                                                {Ref, generalize(subst:apply(Subst, T))}
                                        end
                                end)),
                            ?LOG_DEBUG("Environment:~n~s", [pretty:render_fun_env(ResultEnv)]),
                            ResultEnv
                    end)
        end, % of case
    case length(ResultEnvs) of
        0 ->
            errors:ty_error(Loc,
                            "Could not infer types for recursive functions ~s",
                            FunsStr);
        N ->
            ?LOG_INFO("Inferred ~w possible environments for functions ~s",
                      N, FunsStr),
            ResultEnvs
    end.

% more_general(L, T1, T2, Sym) return true of T1 is more general than T2
-spec more_general(ast:loc(), ast:ty_scheme(), ast:ty_scheme(), symtab:t()) -> boolean().
more_general(Loc, Ts1, Ts2, Tab) ->
    % Ts1 is more general than Ts2 iff for every instantiation Mono2 of Ts2, there
    % exists an instantition Mono1 of Ts1 such that Mono1 <= Mono2.
    % A flexible instantiation of Ts1 with type variables that can be further instantiated by tally
    {Mono1, _, Next} = typing_common:mono_ty(Loc, Ts1, 0),
    % Arbitrary instantiation of Ts2, the type variables A2 are fix
    {Mono2, A2, _} = typing_common:mono_ty(Loc, Ts2, Next),
    C = {scsubty, sets:new(), Mono1, Mono2},
    {SatisfyRes, Delta} = utils:timing(fun() -> tally:is_satisfiable(Tab, sets:from_list([C]), A2) end),
    ?LOG_DEBUG("Tally time: ~pms", Delta),
    Result =
        case SatisfyRes of
            {false, _} -> false;
            _ -> true
        end,
    ?LOG_DEBUG("T1=~s (Mono1=~s) is more general than T2=~s (Mono2=~s): ~s",
        pretty:render_tyscheme(Ts1), pretty:render_ty(Mono1),
        pretty:render_tyscheme(Ts2), pretty:render_ty(Mono2),
        Result),
    Result.

% Generalize generalizes the type of a top-level function. As there is no outer
% environment, we may simply quantify over all free type variables.
-spec generalize(ast:ty()) -> ast:ty_scheme().
generalize(T) ->
    Free = sets:to_list(ftv(T)),
    Vars = lists:map(fun(Alpha) -> {Alpha, {predef, any}} end, Free),
    {ty_scheme, Vars, T}.

-spec ftv(ast:ty()) -> sets:set(ast:ty_varname()).
ftv(T) ->
    L =
        utils:everything(
          fun(X) ->
                  case X of
                      {var, Alpha} -> {ok, Alpha};
                      _ -> error
                  end
          end,
          T),
    sets:from_list(L).
