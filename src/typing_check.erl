-module(typing_check).

-export([
    check_all/4,
    check_all_report/4
]).

-ifdef(TEST).
-export([
    check/3
   ]).
-endif.

-define(TIME(T), begin erlang:system_time(millisecond) - T end).

-include("log.hrl").
-include("typing.hrl").
-include("etylizer.hrl").

% Checks all functions against their specs, only print a report.
% Returns the list of functions that failed type checking.
-spec check_all_report(
        ctx(), string(), symtab:fun_env(), [{ast:fun_decl(), ast:ty_scheme()}]
       ) -> [{atom(), arity()}].
check_all_report(Ctx, FileName, Env, Decls) ->
    ?LOG_NOTE("Checking ~w functions in ~s against their specs", length(Decls), FileName),
    ExtSymtab = symtab:extend_symtab_with_fun_env(Env, Ctx#ctx.symtab),
    ExtCtx = Ctx#ctx { symtab = ExtSymtab },
    BaseName = filename:basename(filename:rootname(FileName)),
    lists:filtermap(
        fun({Decl, Ty}) ->
            case check_one_report(ExtCtx, BaseName, Decl, Ty) of
                ok -> false;
                {error, FA} -> {true, FA}
            end
        end,
        Decls
    ).

-spec check_one_report(ctx(), string(), ast:fun_decl(), ast:ty_scheme()) -> ok | {error, {atom(), arity()}}.
check_one_report(ExtCtx, BaseName, Decl = {function, _, Name, Arity, _}, Ty) ->
    T0 = erlang:system_time(millisecond),
    try check_report(ExtCtx, Decl, Ty) of
        success ->
            io:format(user,"Ok: ~s:~w/~w (~p ms)~n", [BaseName, Name, Arity, ?TIME(T0)]),
            ok;
        timeout ->
            io:format(user,"Timeout: ~s:~w/~w (~p ms)~n", [BaseName, Name, Arity, ?TIME(T0)]),
            {error, {Name, Arity}}
    catch
        throw:Thrown ->
            check_one_report_thrown(?assert_type(Thrown, tuple()), BaseName, Name, Arity, T0),
            {error, {Name, Arity}};
        _:T ->
            io:format(user,"Other: (~p) ~s:~w/~w (~p ms)~n", [{T}, BaseName, Name, Arity, ?TIME(T0)]),
            {error, {Name, Arity}}
    end.

-spec check_one_report_thrown(tuple(), string(), atom(), arity(), integer()) -> ok.
check_one_report_thrown({etylizer, ty_error, Msg}, BaseName, Name, Arity, T0) ->
    io:format(user,"Error: ~s:~w/~w (~p ms)~n  ~s~n", [BaseName, Name, Arity, ?TIME(T0), Msg]);
check_one_report_thrown({etylizer, unsupported, Msg}, BaseName, Name, Arity, _T0) ->
    io:format(user,"Unsupported: ~s:~w/~w~n  ~s~n", [BaseName, Name, Arity, Msg]);
check_one_report_thrown({etylizer, Type, _Msg}, BaseName, Name, Arity, T0) ->
    io:format(user,"Error: (~p) ~s:~w/~w (~p ms)~n", [Type, BaseName, Name, Arity, ?TIME(T0)]);
check_one_report_thrown(Other, BaseName, Name, Arity, T0) ->
    io:format(user,"Other: (~p) ~s:~w/~w (~p ms)~n", [{Other}, BaseName, Name, Arity, ?TIME(T0)]).

% Checks a function against its spec, skips timeouts and does not report errors.
-spec check_report(ctx(), ast:fun_decl(), ast:ty_scheme()) -> success | timeout.
check_report(Ctx, Decl = {function, Loc, Name, Arity, _}, PolyTy) ->
    ?LOG_INFO("Type checking ~w/~w at ~s against type ~s",
              Name, Arity, ast:format_loc(Loc), pretty:render_tyscheme(PolyTy)),
    case utils:timeout(Ctx#ctx.report_timeout, fun() -> check(Ctx, Decl, PolyTy) end) of
        timeout -> timeout;
        {ok, ok} -> success
    end.

% Checks all functions against their specs.
-spec check_all(
        ctx(), string(), symtab:fun_env(), [{ast:fun_decl(), ast:ty_scheme()}]
       ) -> ok | {error, string()}.
check_all(Ctx, FileName, Env, Decls) ->
    ?LOG_INFO("Checking ~w functions in ~s against their specs", length(Decls), FileName),
    ?LOG_DEBUG("Environment: ~s", pretty:render_fun_env(Env)),
    ExtSymtab = symtab:extend_symtab_with_fun_env(Env, Ctx#ctx.symtab),
    ExtCtx = Ctx#ctx { symtab = ExtSymtab },
    check_all_try(ExtCtx, FileName, Decls).

-spec check_all_try(ctx(), string(), [{ast:fun_decl(), ast:ty_scheme()}]) -> ok | {error, string()}.
check_all_try(ExtCtx, FileName, Decls) ->
    try
        lists:foreach(
          fun({Decl, Ty}) -> check(ExtCtx, Decl, Ty) end,
          Decls
         ),
        ?LOG_NOTE("Successfully checked functions in ~s against their specs", FileName),
        ok
    catch throw:Thrown ->
            {etylizer, ty_error, Msg} = ?assert_type(Thrown, {etylizer, ty_error, string()}),
            ?LOG_NOTE("Checking failed: ~s", Msg),
            {error, Msg}
    end.

% Ensures that a mono type used as a spec is supported. Throws a ty_error if not.
-spec ensure_type_supported(ast:loc(), ast:ty()) -> _.
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
check(Ctx, Decl = {function, Loc, Name, Arity, _Clauses}, PolyTy) ->
    ?LOG_INFO("Type checking ~w/~w at ~s against type ~s",
              Name, Arity, ast:format_loc(Loc), pretty:render_tyscheme(PolyTy)),
    {MonoTy, Fixed, _} = typing_common:mono_ty(Loc, PolyTy, Ctx#ctx.symtab),
    ensure_type_supported(Loc, MonoTy),
    AltTys =
        case MonoTy of
            {intersection, L} -> L;
            _ -> [MonoTy]
        end,
    ?LOG_DEBUG("AltTys=~200p,~nMonoTy=~200p", AltTys, MonoTy),
    check_alts(Ctx, Decl, Loc, Name, Arity, PolyTy, AltTys, Fixed).

-spec check_alts(ctx(), ast:fun_decl(), ast:loc(), atom(), arity(), ast:ty_scheme(), [ast:ty()], sets:set(ast:ty_varname())) -> ok.
check_alts(Ctx, Decl = {function, _Loc, _Name, _Arity, Clauses}, Loc, Name, Arity, PolyTy, AltTys, Fixed) ->
    FunStr = utils:sformat("~w/~w", Name, Arity),
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
    UnmatchedEverywhere = intersect_unmatched(Clauses, UnmatchedList),
    case sets:to_list(UnmatchedEverywhere) of
        [] ->
            ?LOG_INFO("Type ok for ~w/~w at ~s", Name, Arity, ast:format_loc(Loc)),
            ok;
        [First | _Rest] ->
            report_tyerror(FunStr, redundant_branch, First, "")
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
    SimpConstrs = check_alt_gen_constrs(Ctx, Decl, FunTy),
    Tab = Ctx#ctx.symtab,
    ?LOG_TRACE("Simplified constraint set for ~s, now " ++
                "checking constraints for satisfiability.~nFixed tyvars: ~w~nConstraints:~n~s",
                FunStr, sets:to_list(Fixed), pretty:render_constr(SimpConstrs)),
    Res =
        case BranchMode of
            unmatched_branch_fail ->
                constr_solve:check_simp_constrs(Tab, Fixed, SimpConstrs, FunStr);
            unmatched_branch_ignore ->
                constr_solve:check_simp_constrs_return_unmatched(Tab, Fixed, SimpConstrs, FunStr)
        end,
    check_alt_result(?assert_type(Res, {ok, sets:set(ast:loc())} | ok | {error, constr_solve:error() | none}),
                     Name, Arity, Loc, FunTy, utils:sformat("~w/~w", Name, Arity)).

-spec check_alt_gen_constrs(ctx(), ast:fun_decl(), ast:ty_full_fun()) -> constr:simp_constrs().
check_alt_gen_constrs(Ctx, Decl, FunTy) ->
    Cs = constr_gen:gen_constrs_annotated_fun(Ctx#ctx.exhaustiveness_mode, Ctx#ctx.symtab, Ctx#ctx.disable_exhaustiveness, FunTy, Decl),
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
    SimpConstrs.

-spec check_alt_result(
    ok | {ok, sets:set(ast:loc())} | {error, constr_solve:error() | none},
    atom(), arity(), ast:loc(), ast:ty_full_fun(), string()) -> {ok, sets:set(ast:loc())}.
check_alt_result(ok, Name, Arity, Loc, FunTy, _FunStrShort) ->
    ?LOG_INFO("Success: function ~w/~w at ~s has type ~s.",
               Name, Arity, ast:format_loc(Loc), pretty:render_ty(FunTy)),
    {ok, sets:new([{version, 2}])};
check_alt_result({ok, Unmatched}, Name, Arity, Loc, FunTy, _FunStrShort) ->
    ?LOG_INFO("Success: function ~w/~w at ~s has type ~s. Unmatched branches: ~s",
               Name, Arity, ast:format_loc(Loc), pretty:render_ty(FunTy),
               pretty:render_set(fun pretty:loc/1, Unmatched)),
    {ok, Unmatched};
check_alt_result({error, none}, Name, Arity, Loc, FunTy, _FunStrShort) ->
    errors:ty_error(Loc, "function ~w/~w failed to type check against type ~s~n~s",
            [Name, Arity, pretty:render_ty(FunTy), typing_common:format_src_loc(Loc)]);
check_alt_result({error, {Kind, Loc2, Hint}}, _Name, _Arity, _Loc, _FunTy, FunStrShort) ->
    report_tyerror(FunStrShort, Kind, Loc2, Hint).

-spec tyerror_msg(constr_error_locs:constr_error_kind()) -> string().
tyerror_msg(Kind) ->
    case Kind of
        tyerror -> "expression failed to type check";
        redundant_branch -> "this branch never matches";
        non_exhaustive_case -> "not all cases are covered";
        nominal_incompatible -> "incompatible nominal types"
    end.

-spec report_tyerror(string(), constr_error_locs:constr_error_kind(), ast:loc(), string()) -> no_return().
report_tyerror(FunName, Kind, Loc, Hint) ->
    SrcCtx = typing_common:format_src_loc(Loc),
    case Hint of
        "" -> errors:ty_error(Loc, "in ~s, ~s~n~s", [FunName, tyerror_msg(Kind), SrcCtx]);
        _ -> errors:ty_error(Loc, "in ~s, ~s~n~s~n~n  ~s", [FunName, tyerror_msg(Kind), SrcCtx, Hint])
    end.

-spec intersect_unmatched([ast:fun_clause()], [sets:set(ast:loc())]) -> sets:set(ast:loc()).
intersect_unmatched(Clauses, UnmatchedList) ->
    {SublocationMap, _} = extract_loc(Clauses),
    UnmatchedListTransitive = lists:map(
      fun(UnmatchedSet) ->
          sets:fold(fun(LLoc, Acc) ->
              Sublocs = sets:from_list(maps:get(LLoc, SublocationMap, [])),
              sets:union(Acc, Sublocs)
          end, UnmatchedSet, UnmatchedSet)
      end,
      UnmatchedList),
    sets:intersection(?assert_type(UnmatchedListTransitive, nonempty_list(sets:set(ast:loc())))).

% Single-pass traversal that returns {Map, Locs} where Map maps each branching
% location to all descendant locations, and Locs is the list of all locations
% found in the subtree (so parents can populate their entry without re-traversing).
-spec extract_loc(any()) -> {#{ast:loc() => [ast:loc()]}, [ast:loc()]}.
extract_loc(TermList) when is_list(TermList) ->
    lists:foldl(fun(T, {MapAcc, LocsAcc}) ->
        {M, L} = extract_loc(T),
        {maps:merge(MapAcc, M), LocsAcc ++ L}
    end, {#{}, []}, TermList);
extract_loc({loc, _, _, _, _, _} = Loc) ->
    {#{}, [Loc]};
extract_loc(Term) when is_tuple(Term) ->
    case Term of
        {'case', Loc, Expr, Clauses} ->
            {Map, ChildLocs} = extract_loc([Expr, Clauses]),
            {maps:put(Loc, ChildLocs, Map), [Loc | ChildLocs]};
        {'fun', Loc, _, Clauses} ->
            {Map, ChildLocs} = extract_loc(Clauses),
            {maps:put(Loc, ChildLocs, Map), [Loc | ChildLocs]};
        {case_clause, Loc, Pat, _Guards, Body} ->
            {Map, ChildLocs} = extract_loc([Pat, Body]),
            {maps:put(Loc, ChildLocs, Map), [Loc | ChildLocs]};
        {fun_clause, Loc, Pats, _Guards, Body} ->
            {Map, ChildLocs} = extract_loc([Pats, Body]),
            {maps:put(Loc, ChildLocs, Map), [Loc | ChildLocs]};
        _ ->
            extract_loc(tuple_to_list(Term))
    end;
extract_loc(_) ->
    {#{}, []}.
