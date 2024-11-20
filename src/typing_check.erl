-module(typing_check).

-export([
    check_all/4,
    check/3
]).

-include("log.hrl").
-include("typing.hrl").

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
        ?LOG_NOTE("Successfully checked functions in ~s against their specs", FileName),
        ok
    catch throw:{ety, ty_error, Msg} ->
            ?LOG_NOTE("Checking failed: ~s", Msg),
            {error, Msg}
    end.

% Ensures that a mono type used as a spec is supported. Throws a ty_error if not.
-spec ensure_type_supported(ast:loc(), ast:ty()) -> ok.
ensure_type_supported(Loc, T) ->
    utils:everywhere(
        fun(InnerT) ->
            % The return value error means: check recursively, no error here
            case InnerT of
                {map, []} -> error;
                {map, [{map_field_opt, _, _}]} -> error;
                {map, [{map_field_req, _, _}]} ->
                    errors:ty_error(Loc, "map types with mandatory associations are not supported");
                {map, _} ->
                    errors:ty_error(Loc, "map types with more than one association are not supported");
                _ -> error
            end
        end,
        T).

% Checks a function against its spec. Throws a ty_error.
% The type scheme comes from a type annotation, that it has the form
% FORALL A . T1 /\ ... /\/ Tn where the Ti are function types
-spec check(ctx(), ast:fun_decl(), ast:ty_scheme()) -> ok.
check(Ctx, Decl = {function, Loc, Name, Arity, _}, PolyTy) ->
    ?LOG_INFO("Type checking ~w/~w at ~s against type ~s",
              Name, Arity, ast:format_loc(Loc), pretty:render_tyscheme(PolyTy)),
    {MonoTy, Fixed, _} = typing_common:mono_ty(PolyTy),
    ensure_type_supported(Loc, MonoTy),
    AltTys =
        case MonoTy of
            {intersection, L} -> L;
            _ -> [MonoTy]
        end,
    ?LOG_DEBUG("AltTys=~200p,~nMonoTy=~200p", AltTys, MonoTy),
    BranchMode =
        case AltTys of
            [_] -> unmatched_branch_fail;
            [] ->
                ?LOG_DEBUG("Invalid spec for ~w/~w: ~w", Name, Arity, PolyTy),
                errors:ty_error(Loc, "Invalid spec for ~w/~w: ~w", [Name, Arity, PolyTy]);
            _ -> unmatched_branch_ignore
        end,
    UnmatchedList = lists:map(
      fun(Ty) ->
            case Ty of
                {fun_full, _, _} ->
                    {ok, Unmatched} = check_alt(Ctx, Decl, Ty, BranchMode, Fixed),
                    Unmatched;
                _ ->
                    ?LOG_DEBUG("Invalid spec for ~w/~w: ~w. Ty=~w", Name, Arity, PolyTy, Ty),
                    errors:ty_error(Loc, "Invalid spec for ~w/~w: ~w", [Name, Arity, PolyTy])
            end
      end,
      AltTys),
    UnmatchedEverywhere = sets:intersection(UnmatchedList),
    case sets:to_list(UnmatchedEverywhere) of
        [] ->
            ?LOG_INFO("Type ok for ~w/~w at ~s", Name, Arity, ast:format_loc(Loc)),
            ok;
        [First | _Rest] ->
            report_tyerror(redundant_branch, First, "")
    end.

-type unmatched_branch_mode() ::
    unmatched_branch_fail       % throw a type error if a branch never matches
    | unmatched_branch_ignore.  % ignore if a branch never matches (for intersection types)

% Checks a function against an alternative of an intersection type.
-spec check_alt(ctx(), ast:fun_decl(), ast:ty_full_fun(), unmatched_branch_mode(),
    sets:set(ast:ty_varname())) -> {ok, Unmachted::sets:set(ast:loc())}.
check_alt(Ctx, Decl = {function, Loc, Name, Arity, _}, FunTy, BranchMode, Fixed) ->
    FunStr = utils:sformat("~w/~w at ~s", Name, Arity, ast:format_loc(Loc)),
    ?LOG_INFO("Checking function ~s against type ~s",
               FunStr, pretty:render_ty(FunTy)),
    Cs = constr_gen:gen_constrs_annotated_fun(Ctx#ctx.symtab, FunTy, Decl),
    case Ctx#ctx.sanity of
        {ok, TyMap} -> constr_gen:sanity_check(Cs, TyMap);
        error -> ok
    end,
    ?LOG_DEBUG("Constraints:~n~s", pretty:render_constr(Cs)),
    Tab = Ctx#ctx.symtab,
    SimpCtx = constr_simp:new_ctx(Tab, #{}, Ctx#ctx.sanity),
    SimpConstrs = constr_simp:simp_constrs(SimpCtx, Cs),
    case Ctx#ctx.sanity of
        {ok, TyMap2} -> constr_simp:sanity_check(SimpConstrs, TyMap2);
        error -> ok
    end,
    ?LOG_TRACE("Simplified constraint set for ~s, now " ++
                "checking constraints for satisfiability.~nFixed tyvars: ~w~nConstraints:~n~s",
                FunStr,
                sets:to_list(Fixed),
                pretty:render_constr(SimpConstrs)),
    Res =
        case BranchMode of
            unmatched_branch_fail ->
                constr_solve:check_simp_constrs(Tab, Fixed, SimpConstrs, FunStr);
            unmatched_branch_ignore ->
                constr_solve:check_simp_constrs_return_unmatched(Tab, Fixed, SimpConstrs, FunStr)
        end,
    case Res of
        ok ->
            ?LOG_INFO("Success: function ~w/~w at ~s has type ~s.",
                       Name,
                       Arity,
                       ast:format_loc(Loc),
                       pretty:render_ty(FunTy)),
            {ok, sets:new([{version, 2}])};
        {ok, Unmatched} ->
            ?LOG_INFO("Success: function ~w/~w at ~s has type ~s. Unmatched branches: ~s",
                       Name,
                       Arity,
                       ast:format_loc(Loc),
                       pretty:render_ty(FunTy),
                       pretty:render_set(fun pretty:loc/1, Unmatched)),
            {ok, Unmatched};
        {error, Err} ->
            case Err of
                none ->
                    errors:ty_error(Loc, "function ~w/~w failed to type check against type ~s~n~s",
                            [Name, Arity, pretty:render_ty(FunTy),
                                typing_common:format_src_loc(Loc)]);
                {Kind, Loc2, Hint} ->
                    report_tyerror(Kind, Loc2, Hint)
            end
    end.

-spec tyerror_msg(constr_error_locs:constr_error_kind()) -> string().
tyerror_msg(Kind) ->
    case Kind of
        tyerror -> "expression failed to type check";
        redundant_branch -> "this branch never matches";
        non_exhaustive_case -> "not all cases are covered"
    end.

-spec report_tyerror(constr_error_locs:constr_error_kind(), ast:loc(), string()) -> no_return().
report_tyerror(Kind, Loc, Hint) ->
    SrcCtx = typing_common:format_src_loc(Loc),
    case Hint of
        "" -> errors:ty_error(Loc, "~s~n~s", [tyerror_msg(Kind), SrcCtx]);
        _ -> errors:ty_error(Loc, "~s~n~s~n~n  ~s", [tyerror_msg(Kind), SrcCtx, Hint])
    end.
