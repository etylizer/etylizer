-module(typing).

-export([
    infer/2,
    check/3,
    more_general/3,
    check_forms/3,
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

% Infers the types of a group of mutually recursive functions. Throws a ty_error.
% FIXME: must return multiple possible type environments
-spec infer(ctx(), [ast:fun_decl()]) -> [{ast:global_ref(), Type::ast:ty_scheme()}].
infer(_, []) -> errors:bug("typing:infer called with empty list of declarations");
infer(Ctx, Decls) ->
    {Cs, Env} = constr_gen:gen_constrs_fun_group(Decls),
    case Ctx#ctx.sanity of
        {ok, TyMap} -> constr_gen:sanity_check(Cs, TyMap);
        error -> ok
    end,
    PolyEnv = maps:map(fun(_Key, T) -> {ty_scheme, [], T} end, Env),
    Tab = Ctx#ctx.symtab,
    SimpCtx = constr_simp:new_ctx(Tab, PolyEnv, Ctx#ctx.sanity, report),
    Funs =
        lists:map(
            fun({function, _Loc, Name, Arity, _}) ->
                    utils:sformat("~w/~w", Name, Arity)
            end,
            Decls),
    Dss = report_tyerror(constr_simp:simp_constrs(SimpCtx, Cs),
        utils:sformat("while infering types of mutually recursive functions ~w", Funs)),
    [Ds | _] = Dss, % FIXME: this is wrong but for now we do not use infer
    case tally:tally(Tab, Ds) of
        [] ->
            Loc =
                case Decls of
                    [{function, L, _, _, _} | _] -> L
                end,
            errors:ty_error(Loc,
                            "Error when infering type of mutually recursive functions ~w", Funs);
        % FIXME: this is wrong, we must non-deterministically try out all substitutions returned
        % by tally.
        [Subst | _] ->
            lists:map(
              fun({function, _Loc, Name, Arity, _}) ->
                      Ref = {ref, Name, Arity},
                      case maps:find(Ref, Env) of
                          error -> errors:bug("Function ~w/~w not found in env", [Name, Arity]);
                          {ok, T} ->
                              {Ref, generalize(subst:apply(Subst, T))}
                      end
              end,
              Decls)
    end.

-spec check_forms(ctx(), ast:forms(), sets:set(string())) -> ok.
check_forms(Ctx, Forms, Only) ->
    ExtTab = symtab:extend_symtab(Forms, Ctx#ctx.symtab),
    ExtCtx = Ctx#ctx { symtab = ExtTab },
    DefinedFuns =
        lists:filtermap(
          fun(Form)->
                  case Form of
                      {function, Loc, Name, Arity, _Clauses} ->
                          Ref = {ref, Name, Arity},
                          RefStr = utils:sformat("~w/~w", Name, Arity),
                          NameStr = utils:sformat("~w", Name),
                          case sets:is_empty(Only) orelse sets:is_element(RefStr, Only)
                                orelse sets:is_element(NameStr, Only) of
                              true ->
                                  case symtab:find_fun(Ref, ExtTab) of
                                      error ->
                                          ?LOG_WARN("~s: function ~s has no type spec, not checking!",
                                                    ast:format_loc(Loc), RefStr);
                                      {ok, Ty} ->
                                          check(ExtCtx, Form, Ty)
                                  end;
                              false -> ?LOG_DEBUG("~s: not type checking function ~s as requested",
                                                  ast:format_loc(Loc), RefStr)
                          end,
                          {true, {RefStr, NameStr}};
                      _ -> false
                  end
          end,
          Forms),
    {WithArity, JustNames} = lists:unzip(DefinedFuns),
    Unknowns = sets:subtract(Only, sets:union(sets:from_list(WithArity), sets:from_list(JustNames))),
    case sets:is_empty(Unknowns) of
        true -> ok;
        false ->
            ?LOG_WARN("Unknown functions in only: ~200p", sets:to_list(Unknowns))
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

-spec check_alt(ctx(), ast:fun_decl(), ast:ty_full_fun(), constr_simp:unmatched_branch_mode()) -> ok.
check_alt(Ctx, Decl = {function, Loc, Name, Arity, _}, FunTy, BranchMode) ->
    Cs = constr_gen:gen_constrs_annotated_fun(FunTy, Decl),
    case Ctx#ctx.sanity of
        {ok, TyMap} -> constr_gen:sanity_check(Cs, TyMap);
        error -> ok
    end,
    ?LOG_INFO("Checking function ~w/~w at ~s against type ~s",
               Name,
               Arity,
               ast:format_loc(Loc),
               pretty:render_ty(FunTy)),
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
                          Substs = tally:tally(Tab, Ds, FreeSet),
                          case Substs of
                              {error, ErrList} ->
                                  {ErrListShort, N} = utils:shorten(ErrList, 20),
                                  ErrStr =
                                      utils:sformat("  Errors for constraint set ~w:~n", Idx) ++
                                      string:join(
                                        lists:map(
                                          fun({error, Msg}) -> "    " ++ Msg end, ErrListShort),
                                        "\n") ++
                                      (if N =:= 0 -> "";
                                          true -> utils:sformat("~n    (skipped ~w lines)", N)
                                       end),
                                  ?LOG_DEBUG("tally finished with errors: ~s", ErrStr),
                                  {false, Idx + 1};
                              [S] ->
                                  ?LOG_DEBUG("Unique substitution:~n~s", [pretty:render_subst(S)]),
                                  {true, Idx + 1};
                              L ->
                                  ?LOG_DEBUG("~w substitutions: ~200p", length(L), pretty:render_substs(L)),
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
                  {[ {Alpha, ast:mk_intersection([{var, AlphaFresh}, Bound])} | Kvs],
                   [ AlphaFresh | Freshs ],
                   NextI}
          end,
          {[], [], FreshStart},
          Tyvars
         ),
    Subst = subst:from_list(Kvs),
    Res = subst:apply(Subst, T),
    ?LOG_DEBUG("Result of monomorphizing type scheme ~s:~n~s",
               pretty:render_tyscheme(TyScm), pretty:render_ty(Res)),
    {Res, sets:from_list(Freshs), I}.

% more_general(T1, T2, Sym) return true of T1 is more general than T2
-spec more_general(ast:ty_scheme(), ast:ty_scheme(), symtab:t()) -> boolean().
more_general(Ts1, Ts2, Tab) ->
    {Mono1, _, Next} = mono_ty(Ts1, 0),
    {Mono2, A2, _} = mono_ty(Ts2, Next),
    C = {csubty, sets:new(), Mono1, Mono2},
    case tally:tally(Tab, sets:from_list([C]), A2) of
        [] -> false;
        _ -> true
    end.

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
