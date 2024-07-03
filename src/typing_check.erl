-module(typing_check).

-export([
    check_all/4,
    check/3
]).

-export_type([ctx/0]).

-include_lib("log.hrl").
-include_lib("typing.hrl").

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
    MonoTy = typing_common:mono_ty(PolyTy),
    AltTys =
        case MonoTy of
            {intersection, L} -> L;
            _ -> [MonoTy]
        end,
    BranchMode =
        case AltTys of
            [_] -> unmatched_branch_report;
            [] ->
                errors:ty_error(Loc, "Invalid spec for ~w/~w: ~w", [Name, Arity, PolyTy]);
            _ -> unmatched_branch_ignore
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
check_alt(Ctx, Decl = {function, Loc, Name, Arity, _}, FunTy, _BranchMode) ->
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
    FreeSet = tyutils:free_in_ty(FunTy),
    SimpCtx = constr_simp:new_ctx(Tab, #{}, Ctx#ctx.sanity),
    SimpConstrs = constr_simp:simp_constrs(SimpCtx, Cs),
    case Ctx#ctx.sanity of
        {ok, TyMap2} -> constr_simp:sanity_check(SimpConstrs, TyMap2);
        error -> ok
    end,
    ?LOG_DEBUG("Simplified constraint set for ~w/~w at ~s, now " ++
                "checking constraints for satisfiability.~nFixed tyvars: ~w~nConstraints:~n~s",
                Name, Arity, ast:format_loc(Loc),
                sets:to_list(FreeSet),
                pretty:render_constr(SimpConstrs)),
    Res = constr_solve:check_simp_constrs(Tab, FreeSet, SimpConstrs),
    case Res of
        ok ->
            ?LOG_INFO("Success: function ~w/~w at ~s has type ~s.",
                       Name,
                       Arity,
                       ast:format_loc(Loc),
                       pretty:render_ty(FunTy));
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

-spec tyerror_msg(constr_simp:simp_constrs_error_kind()) -> string().
tyerror_msg(Kind) ->
    case Kind of
        tyerror -> "expression failed to type check";
        redundant_branch -> "this branch never matches";
        non_exhaustive_case -> "not all cases are covered"
    end.

-spec report_tyerror(constr_simp:simp_constrs_error_kind(), ast:loc(), string()) -> no_return().
report_tyerror(Kind, Loc, Hint) ->
    SrcCtx = typing_common:format_src_loc(Loc),
    case Hint of
        "" -> errors:ty_error(Loc, "~s~n~s", [tyerror_msg(Kind), SrcCtx]);
        _ -> errors:ty_error(Loc, "~s~n~s~n~n  ~s", [tyerror_msg(Kind), SrcCtx, Hint])
    end.
