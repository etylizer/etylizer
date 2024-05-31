-module(typing).

-export([
    infer/2,
    check/3,
    more_general/3,
    check_forms/4,
    new_ctx/2
]).

-export_type([ctx/0]).

-include_lib("log.hrl").

-record(ctx,
        { symtab :: symtab:t(),
          sanity :: t:opt(ast_check:ty_map())
        }).
-opaque ctx() :: #ctx{}.

-spec new_ctx(symtab:t(), t:opt(ast_check:ty_map())) -> ctx().
new_ctx(Tab, Sanity) ->
    Ctx = #ctx{ symtab = Tab, sanity = Sanity },
    Ctx.

-spec format_src_loc(ast:loc()) -> string().
format_src_loc({loc, File, LineNo, ColumnNo}) ->
    ErrMsg = "",
    case utils:file_get_lines(File) of
        {error, _} -> ErrMsg;
        {ok, Lines} ->
            N = length(Lines),
            if
                LineNo >= 1 andalso LineNo =< N ->
                    Line = string:trim(lists:nth(LineNo, Lines), trailing),
                    ColumnSpace = lists:duplicate(ColumnNo - 1, $\s),
                    utils:sformat("%~5.B| ~s~n%     | ~s^", LineNo, Line, ColumnSpace);
                true ->
                    ErrMsg
            end
    end.

-spec report_tyerror(constr_simp:simp_constrs_result(), string()) -> nonempty_list(constr:simp_constrs()).
report_tyerror({simp_constrs_ok, L}, _) ->
    case length(L) of
        0 -> errors:bug("empty list of simple constraints returned from constr_simp:simp_constrs");
        _ -> L
    end;
report_tyerror({simp_constrs_error, {Kind, Loc}}, What) ->
    Msg =
        case Kind of
            tyerror -> "expression failed to type check";
            redundant_branch -> "this branch never matches";
            non_exhaustive_case -> "not all cases are covered"
        end,
    SrcCtx = format_src_loc(Loc),
    errors:ty_error(Loc, "~s~n~s~n~n  ~s", [Msg, SrcCtx, What]).


% Checks all forms of a module
-spec check_forms(ctx(), string(), ast:forms(), sets:set(string())) -> ok.
check_forms(Ctx, FileName, Forms, Only) ->
    ExtTab = symtab:extend_symtab(Forms, Ctx#ctx.symtab),
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
    InferredTyEnvs = infer_all(ExtCtx, FileName, FunsWithoutSpec),
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
                        case check_all(ExtCtx, FileName, E, FunsWithSpec) of
                            ok -> ok; % we are done
                            {error, Msg} -> Loop(RestEnvs, [{E, Msg} | Errs])
                        end
                end
        end,
    Loop(InferredTyEnvs, []),
    ?LOG_INFO("Checking ~w functions in ~s against their specs finished successfully",
              length(FunsWithSpec), FileName).

% Infers the types of all the given functions.
-spec infer_all(ctx(), string(), [ast:fun_decl()]) -> [symtab:fun_env()].
infer_all(Ctx, FileName, Decls) ->
    ?LOG_INFO("Inferring types of functions without specs in ~s", FileName),
    % FIXME: need to build strongly connected components to infer each group in isolation
    L =
        case Decls of
            [] -> [#{}];
            _ -> infer(Ctx, Decls)
        end,
    ?LOG_INFO("Inferring types of functions without specs returned ~w environments in total",
              length(L)),
    L.

% Infers the types of a group of (mutually recursive) functions.
% For reasons of non-determinism, return a list of possible type
% environments for these functions.
% Throws a ty_error if no such environment exist.
-spec infer(ctx(), [ast:fun_decl()]) -> [symtab:fun_env()].
infer(_, []) -> errors:bug("typing:infer called with empty list of declarations");
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
    SimpCtx = constr_simp:new_ctx(Tab, PolyEnv, Ctx#ctx.sanity, report),
    Funs =
        lists:map(
            fun({function, _Loc, Name, Arity, _}) ->
                    utils:sformat("~w/~w", Name, Arity)
            end,
            Decls),
    % FIXME bad argument exception io_lib:format/2
    Dss = report_tyerror(constr_simp:simp_constrs(SimpCtx, Cs), "error"),
    %utils:sformat("while infering types of mutually recursive functions ~w", Funs)),
    case Ctx#ctx.sanity of
        {ok, TyMap2} -> constr_simp:sanity_check(Dss, TyMap2);
        error -> ok
    end,
    Total = length(Dss),
    if Total =:= 0 ->
            errors:bug("empty list of simple constraints returned from constr_simp:simp_constrs");
       true ->
            ?LOG_DEBUG("Got ~w simplified constraint sets", Total)
    end,
    ResultEnvs = sets:to_list(sets:from_list(utils:flatmap_flip(
      utils:with_index(1, Dss),
      fun({Idx, Ds}) ->
              ?LOG_DEBUG("Simplified constraint set ~w/~w, now " ++
                             "invoking tally on it:~n~s",
                         Idx, Total, pretty:render_constr(Ds)),
              case utils:timing(fun () -> tally:tally(Tab, Ds) end) of
                  {{error, ErrList}, Delta} ->
                      ErrStr = format_tally_error(Idx, ErrList),
                      ?LOG_DEBUG("Tally time: ~pms, tally finished with errors: ~s", Delta, ErrStr),
                      [];
                  {Substs, Delta} ->
                      NumSubsts = length(Substs),
                      utils:map_flip(
                        utils:with_index(1, Substs),
                        fun({SubstIdx, Subst}) ->
                                ?LOG_DEBUG("Tally time: ~pms, substitution ~w/~w:~n~s",
                                           Delta, SubstIdx, NumSubsts,
                                           pretty:render_subst(Subst)),
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
              end % of case
      end))),
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

% Checks all functions against their specs.
-spec check_all(
        ctx(), string(), symtab:fun_env(), [{ast:fun_decl(), ast:ty_scheme()}]
       ) -> ok | {error, string()}.
check_all(Ctx, FileName, Env, Decls) ->
    ?LOG_INFO("Checking ~w functions in ~s against their specs", length(Decls), FileName),
    ?LOG_DEBUG("Environment: ~s", pretty:render_fun_env(Env)),
    ExtCtx = Ctx#ctx { symtab = symtab:extend_symtab_with_fun_env(Env, Ctx#ctx.symtab) },
    try
        lists:foreach(
          fun({Decl, Ty}) -> check(ExtCtx, Decl, Ty) end,
          Decls
         ),
        ?LOG_INFO("Successfully checked functions in ~s against their specs", FileName),
        ok
    catch throw:{ety, ty_error, Msg} ->
            ?LOG_INFO("Checking failed: ~s", Msg),
            {error, Msg}
    end.


% Checks a function against its spec. Throws a ty_error.
% The type scheme comes from a type annotation, that it has the form
% FORALL A . T1 /\ ... /\/ Tn where the Ti are function types
-spec check(ctx(), ast:fun_decl(), ast:ty_scheme()) -> ok.
check(Ctx, Decl = {function, Loc, Name, Arity, _}, PolyTy) ->
    ?LOG_INFO("Type checking ~w/~w at ~s against type ~s",
              Name, Arity, ast:format_loc(Loc), pretty:render_tyscheme(PolyTy)),
    MonoTy = mono_ty(PolyTy),
    AltTys =
        case MonoTy of
            {intersection, L} -> L;
            _ -> [MonoTy]
        end,
    BranchMode =
        case AltTys of
            [_] -> report;
            [] ->
                errors:ty_error(Loc, "Invalid spec for ~w/~w: ~w", [Name, Arity, PolyTy]);
            _ -> ignore_branch
        end,
    lists:foreach(
      fun(Ty) ->
              case Ty of
                  {fun_full, _, _} -> check_alt(Ctx, Decl, Ty, BranchMode);
                  _ ->
                    errors:ty_error(Loc, "Invalid spec for ~w/~w: ~w", [Name, Arity, PolyTy])
              end
      end,
      AltTys),
    ?LOG_INFO("Type ok for ~w/~w at ~s", Name, Arity, ast:format_loc(Loc)),
    ok.

% Checks a function against an alternative of an intersection type.
-spec check_alt(ctx(), ast:fun_decl(), ast:ty_full_fun(), constr_simp:unmatched_branch_mode()) -> ok.
check_alt(Ctx, Decl = {function, Loc, Name, Arity, _}, FunTy, BranchMode) ->
    ?LOG_INFO("Checking function ~w/~w at ~s against type ~s",
               Name,
               Arity,
               ast:format_loc(Loc),
               pretty:render_ty(FunTy)),
    Cs = constr_gen:gen_constrs_annotated_fun(Ctx#ctx.symtab, FunTy, Decl),
    case Ctx#ctx.sanity of
        {ok, TyMap} -> constr_gen:sanity_check(Cs, TyMap);
        error -> ok
    end,
    ?LOG_DEBUG("Constraints:~n~s", pretty:render_constr(Cs)),
    Tab = Ctx#ctx.symtab,
    SimpCtx = constr_simp:new_ctx(Tab, #{}, Ctx#ctx.sanity, BranchMode),
    Dss = report_tyerror(constr_simp:simp_constrs(SimpCtx, Cs),
        utils:sformat("while checking function ~w/~w against type ~s",
            Name, Arity, pretty:render_ty(FunTy))),
    Total = length(Dss),
    {Status, _} =
        lists:foldl(
          fun(Ds, {Status, Idx}) ->
                case Status of
                    true -> {Status, Idx + 1};
                    false ->
                        FreeSet = tyutils:free_in_ty(FunTy),
                        ?LOG_DEBUG("Simplified constraint set ~w/~w for ~w/~w at ~s, now " ++
                                    "invoking tally on it.~nFixed tyvars: ~w~nConstraints:~n~s",
                                    Idx, Total, Name, Arity, ast:format_loc(Loc),
                                    sets:to_list(FreeSet),
                                    pretty:render_constr(Ds)),
                        {Substs, Delta} = utils:timing(fun () -> tally:tally(Tab, Ds, FreeSet) end),
                        case Substs of
                            {error, ErrList} ->
                                ErrStr = format_tally_error(Idx, ErrList),
                                ?LOG_DEBUG("Tally time: ~pms, tally finished with errors: ~s",
                                    Delta, ErrStr),
                                {false, Idx + 1};
                            [S] ->
                                ?LOG_DEBUG("Tally time: ~pms, unique substitution:~n~s",
                                    Delta, [pretty:render_subst(S)]),
                                {true, Idx + 1};
                            L ->
                                ?LOG_DEBUG("Tally time: ~pms, ~w substitutions: ~200p",
                                    Delta, length(L), pretty:render_substs(L)),
                                {true, Idx + 1}
                        end
                end
          end,
          {false, 1},
          Dss),
    case Status of
        true ->
            ?LOG_INFO("Success: function ~w/~w at ~s has type ~s.",
                       Name,
                       Arity,
                       ast:format_loc(Loc),
                       pretty:render_ty(FunTy));
        false ->
            SrcCtx = format_src_loc(Loc),
            errors:ty_error(Loc, "function ~w/~w failed to type check against type ~s~n~s",
                            [Name, Arity, pretty:render_ty(FunTy), SrcCtx])
    end.

-spec format_tally_error(integer(), [string()]) -> string().
format_tally_error(ConstrIdx, ErrList) ->
    {ErrListShort, N} = utils:shorten(ErrList, 20),
    utils:sformat("  Errors for constraint set ~w:~n", ConstrIdx) ++
        string:join(
          lists:map(
            fun({error, Msg}) -> "    " ++ Msg end, ErrListShort),
          "\n") ++
        (if N =:= 0 -> "";
            true -> utils:sformat("~n    (skipped ~w lines)", N)
         end).

% Creates the monomorphic version of the given type scheme, does not
% replace the universally quantified type variables with fresh ones.
-spec mono_ty(ast:ty_scheme()) -> ast:ty().
mono_ty(TyScm) ->
    {U, _, _} = mono_ty(TyScm, no_fresh),
    U.

-spec fresh_tyvar(ast:ty_varname(), integer() | no_fresh) ->
          {ast:ty_varname(), integer() | no_fresh}.
fresh_tyvar(Alpha, no_fresh) -> {Alpha, no_fresh};
fresh_tyvar(Alpha, I) ->
    AlphaFresh = list_to_atom(utils:sformat("~w#~w", Alpha, I)),
    {AlphaFresh, I + 1}.

% Creates the monomorphic version of the given type scheme by replacing
% the universally quantified type variables with fresh type variables.
% The second parameter is the start number for the fresh type variable
% generator.
-spec mono_ty(ast:ty_scheme(), integer() | no_fresh) ->
          {ast:ty(), sets:set(ast:ty_varname()), integer() | no_fresh}.
mono_ty(TyScm = {ty_scheme, Tyvars, T}, FreshStart) ->
    ?LOG_DEBUG("Monomorphizing type scheme ~s", pretty:render_tyscheme(TyScm)),
    {Kvs, Freshs, I} =
        lists:foldl(
          fun({Alpha, Bound}, {Kvs, Freshs, I}) ->
                  {AlphaFresh, NextI} = fresh_tyvar(Alpha, I),
                  {[ {Alpha, ast_lib:mk_intersection([{var, AlphaFresh}, Bound])} | Kvs],
                   [ AlphaFresh | Freshs ],
                   NextI}
          end,
          {[], [], FreshStart},
          Tyvars
         ),
    Subst = subst:from_list(Kvs),
    Res = subst:apply(Subst, T),
    ?LOG_DEBUG("Result of monomorphizing type scheme ~s:~n~s~nFresh: ~200p",
               pretty:render_tyscheme(TyScm), pretty:render_ty(Res), Freshs),
    {Res, sets:from_list(Freshs), I}.

% more_general(T1, T2, Sym) return true of T1 is more general than T2
-spec more_general(ast:ty_scheme(), ast:ty_scheme(), symtab:t()) -> boolean().
more_general(Ts1, Ts2, Tab) ->
    % Ts1 is more general than Ts2 iff for every instantiation Mono2 of Ts2, there
    % exists an instantition Mono1 of Ts1 such that Mono1 <= Mono2.
    % A flexible instantiation of Ts1 with type variables that can be further instantiated by tally
    {Mono1, _, Next} = mono_ty(Ts1, 0),
    % Arbitrary instantiation of Ts2, the type variables A2 are fix
    {Mono2, A2, _} = mono_ty(Ts2, Next),
    C = {csubty, sets:new(), Mono1, Mono2},
    {TallyRes, Delta} = utils:timing(fun() -> tally:tally(Tab, sets:from_list([C]), A2) end),
    ?LOG_DEBUG("Tally time: ~pms", Delta),
    Result =
        case TallyRes of
            {error, _} -> false;
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
