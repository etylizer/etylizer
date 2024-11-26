-module(ast_transform).

-export([
    trans/3, trans/4
]).

-export_type([trans_mode/0]).

-ifdef(TEST).
-export([trans/2]).
-endif.
    
-compile([nowarn_shadow_vars]).

-include("log.hrl").

-record(ctx,
        { path :: file:filename(),
          module_name :: atom(),
          funenv :: funenv(),
          % The records seen so far. We need the record definitions to rewrite record types
          % into tuple types.
          records :: #{ atom() => records:record_ty() }
        }).
-type ctx() :: #ctx{}.

-type tyenv() :: varenv:t(atom(), atom()). % just a set of defined type variables

% An environment for all functions available unqualified in the current module.
% Maps name/arity to intern if the function is defined in the same module, and to
% {extern, ModName} otherwise.
-type funenv() :: varenv:t(ast:fun_with_arity(), intern | {extern, ModName::atom()}).

-spec trans(string(), [ast_erl:form()]) -> [ast:form()].
trans(Path, Forms) -> trans(Path, Forms, full).

% full: everything is transformed
% flat: function bodies are not transformed.
-type trans_mode() :: full | flat.

-spec trans(string(), [ast_erl:form()], trans_mode()) -> [ast:form()].
trans(Path, Forms, Mode) ->
    FunEnv = build_funenv(Path, Forms),
    trans(Path, Forms, Mode, FunEnv).

-spec trans(string(), [ast_erl:form()], trans_mode(), funenv()) -> [ast:form()].
trans(Path, Forms, Mode, FunEnv) ->
    ModName = ast_utils:modname_from_path(Path),
    {RevNewForms, _} =
        lists:foldl(
            fun(F, {NewForms, Ctx}) ->
                case trans_form(Ctx, F, Mode) of
                    error -> {NewForms, Ctx};
                    {NewForm, NewCtx} -> {[NewForm | NewForms], NewCtx};
                    NewForm -> {[NewForm | NewForms], Ctx}
                end
            end,
            {[], #ctx{ path = Path, module_name = ModName, funenv = FunEnv, records = #{} }},
            Forms
            ),
    lists:reverse(RevNewForms).

-spec build_funenv(file:filename(), [ast_erl:form()]) -> funenv().
build_funenv(Path, Forms) ->
    Env1 = lists:foldl(
      fun(Form, E) ->
          case Form of
              {attribute, Anno, import, {ModName, Funs}} ->
                  lists:foldl(
                    fun(FunArity, E0) ->
                        varenv:insert(ast:to_loc(Path, Anno), FunArity, {extern, ModName}, E0)
                    end,
                    E, Funs);
              {function, Anno, Name, Arity, _Clauses} ->
                  varenv:insert(ast:to_loc(Path, Anno), {Name, Arity}, intern, E);
              _ -> E
            end
      end,
      varenv:empty("function"),
      Forms),
    lists:foldl(
        fun({Name, Arity, _}, E) ->
            varenv:insert_if_absent({Name, Arity}, {extern, erlang}, E)
        end, Env1, stdtypes:builtin_funs()).

-spec trans_form(ctx(), ast_erl:form(), trans_mode()) -> {ast:form(), ctx()} | ast:form() | error.
trans_form(Ctx, Form, Mode) ->
    R =
        case Form of
            {attribute, Anno, export, X} -> {attribute, to_loc(Ctx, Anno), export, X};
            {attribute, Anno, export_type, X} -> {attribute, to_loc(Ctx, Anno), export_type, X};
            {attribute, Anno, import, X} -> {attribute, to_loc(Ctx, Anno), import, X};
            {attribute, Anno, module, X} -> {attribute, to_loc(Ctx, Anno), module, X};
            {attribute, _, file, _} -> error;
            {attribute, _, behaviour, _} -> error;
            {attribute, _, behavior, _} -> error;
            {function, Anno, Name, Arity, Clauses} ->
                case Mode of
                    full ->
                        {function, to_loc(Ctx, Anno), Name, Arity, trans_fun_clauses(Ctx, Clauses)};
                    flat ->
                        error
                end;
            {attribute, Anno, spec, {{Name, Arity}, FunTys}} ->
                Loc = to_loc(Ctx, Anno),
                {attribute, Loc, spec, Name, Arity, trans_spec_ty(Ctx, Loc, FunTys), without_mod};
            {attribute, Anno, spec, {{_Mod, Name, Arity}, FunTys}} ->
                Loc = to_loc(Ctx, Anno),
                {attribute, Loc, spec, Name, Arity, trans_spec_ty(Ctx, Loc, FunTys), with_mod};
            {attribute, Anno, callback, {{Name, Arity}, FunTys}} ->
                Loc = to_loc(Ctx, Anno),
                {attribute, Loc, callback, Name, Arity, trans_spec_ty(Ctx, Loc, FunTys),
                 without_mod};
            {attribute, Anno, record, {Name, Fields}} ->
                NewFields = trans_record_fields(Ctx, varenv:empty("type variable"), Fields),
                NewForm = {attribute, to_loc(Ctx, Anno), record, {Name, NewFields}},
                RecordTy = records:record_ty_from_decl(Name, NewFields),
                NewCtx = Ctx#ctx { records = maps:put(Name, RecordTy, Ctx#ctx.records) },
                ?LOG_TRACE("Registered new record type: ~200p", RecordTy),
                {NewForm, NewCtx};
            {attribute, Anno, type, Def} ->
                {attribute, to_loc(Ctx, Anno), type, transparent, trans_tydef(Ctx, Def)};
            {attribute, Anno, opaque, Def} ->
                {attribute, to_loc(Ctx, Anno), type, opaque, trans_tydef(Ctx, Def)};
            {attribute, Anno, Other, _} ->
                ?LOG_TRACE("Ignoring attribute ~w at ~s", Other, ast:format_loc(to_loc(Ctx, Anno))),
                error;
            {warning, _} -> error;
            {eof, _} -> error;
            X -> errors:uncovered_case(?FILE, ?LINE, X)
        end,
    R.

-spec to_loc(ctx(), ast_erl:anno()) -> ast:loc().
to_loc(Ctx, Anno) -> ast:to_loc(Ctx#ctx.path, Anno).

-spec trans_spec_ty(ctx(), ast:loc(), [ast_erl:ty_full_fun()]) -> ast:ty_scheme().
trans_spec_ty(Ctx, Loc, FunTys) ->
    AllTyvars =
        utils:everything(
          fun (V = {var, _, _}) -> {ok, V};
              (_) -> error
          end,
          FunTys),
    {UnconstrFunTys, NestedConstrs} =
        lists:unzip(
          lists:map(
            fun ({type, _Anno, bounded_fun, [Ty, Constrs]}) -> {Ty, Constrs};
                (Ty) -> {Ty, []}
            end, FunTys)),
    Env = make_tyenv(Ctx, AllTyvars, ignore_dups),
    Constrs =
        lists:flatmap(fun(L) -> lists:map(fun (C) -> trans_constraint(Ctx, Env, C) end, L) end,
                      NestedConstrs),
    Tys = lists:map(fun (T) -> trans_ty(Ctx, Env, T) end, UnconstrFunTys),
    Ty =
        case Tys of
            [] -> errors:ty_error(Loc, "invalid spec");
            [T] -> T;
            _ -> {intersection, Tys}
        end,
    TyVars = varenv:range(Env),
    ConstrainedTyVars =
        lists:map(
                fun(Alpha) ->
                        Bounds = lists:filtermap(fun({subty_constraint, _, Beta, T}) ->
                                                         if Alpha =:= Beta -> {true, T};
                                                            true -> false
                                                         end
                                                 end, Constrs),
                        {Alpha, ast_lib:mk_intersection(Bounds)}
                end,
                TyVars),
    {ty_scheme, ConstrainedTyVars, Ty}.

-spec make_tyenv(ctx(), [ast_erl:ty_var()], ignore_dups | fail_dups) -> tyenv().
make_tyenv(Ctx, Tyvars, Mode) ->
    lists:foldl(fun({var, Anno, V}, E) ->
                        Loc = to_loc(Ctx, Anno),
                        case Mode of
                            ignore_dups -> varenv:insert_if_absent(V, V, E);
                            fail_dups -> varenv:insert(Loc, V, V, E)
                        end
                end,
                varenv:empty("type variable"),
                Tyvars).

-spec trans_tydef(ctx(), ast_erl:tydef()) -> ast:tydef().
trans_tydef(Ctx, {Name, Ty, Tyvars}) ->
    % FIXME: check contractiveness and regularity
    Env = make_tyenv(Ctx, Tyvars, fail_dups),
    TyNew = trans_ty(Ctx, Env, Ty),
    TyVars = lists:map(fun({var, _, Alpha}) -> {Alpha, {predef, any}} end, Tyvars),
    {Name, {ty_scheme, TyVars, TyNew}}.

-spec trans_constraint(ctx(), tyenv(), ast_erl:ty_constraint()) -> ast:ty_constraint().
trans_constraint(Ctx, Env, C) ->
    case C of
        {type, Anno, constraint, [{atom, _, is_subtype}, [{var, _, Name}, Ty]]} ->
            {subty_constraint, to_loc(Ctx, Anno), Name, trans_ty(Ctx, Env, Ty)};
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

% support for ety:negation, ety:intersection, and ety:without
-spec resolve_ety_ty(ast:loc(), atom(), [ast:ty()]) -> ast:ty().
resolve_ety_ty(_, negation, [Ty]) -> {negation, Ty};
resolve_ety_ty(_, intersection, Tys) ->
    case Tys of
        [] -> {predef, any};
        [Ty] -> Ty;
        _ -> {intersection, Tys}
    end;
resolve_ety_ty(_, without, [T, U]) -> {intersection, [T, {negation, U}]};
resolve_ety_ty(L, Name, _) ->
    errors:ty_error(L, "Invalid use of builtin type ety:~w", Name).

-spec eval_const_ty(erl_parse:abstract_expr(), ast:loc()) -> {singleton, integer()}.
eval_const_ty(Ty, Loc) ->
    try
        case erl_eval:expr(Ty, maps:new()) of
            {value, Val, _} when is_integer(Val) -> {singleton, Val};
            _ -> errors:ty_error(Loc, "Invalid type: ~200p", Ty)
        end
    catch error:_:_ ->
        errors:ty_error(Loc, "Invalid type: ~200p", Ty)
    end.

-spec trans_ty(ctx(), tyenv(), ast_erl:ty()) -> ast:ty().
trans_ty(Ctx, Env, Ty) ->
    case Ty of
        {ann_type, _, [_, T]} -> trans_ty(Ctx, Env, T);
        {'atom', _, X} -> {singleton, X};
        {'char', _, X} -> {singleton, X};
        {'integer', _, X} -> {singleton, X};
        {type, _, binary, [{'integer', _, X}, {'integer', _, Y}]} -> {binary, X, Y};
        {type, _, nil, []} -> {empty_list};
        {type, _, list, [T]} -> {list, trans_ty(Ctx, Env, T)};
        {type, _, 'fun', []} -> {fun_simple};
        {type, _, 'fun', [{type, _, any}, T]} ->
                case T of
                    {type, _, any} -> errors:bug("Invalid AST");
                    T2 -> {fun_any_arg, trans_ty(Ctx, Env, T2)}
                end;
        {type, _, 'fun', [{type, _, product, ArgTys}, ResTy]} ->
            {fun_full, trans_tys(Ctx, Env, ArgTys), trans_ty(Ctx, Env, ResTy)};
        {type, Anno, bounded_fun, _} ->
            errors:unsupported(to_loc(Ctx, Anno), "nested function types with constraints");
        {type, Anno, range, [T1, T2]} ->
            Loc = to_loc(Ctx, Anno),
            case {trans_ty(Ctx, Env, T1), trans_ty(Ctx, Env, T2)} of
                {{singleton, I1}, {singleton, I2}} when is_integer(I1) andalso is_integer(I2) ->
                    {range, I1, I2};
                _ ->
                    errors:ty_error("~s: Invalid range type: ~w", [ast:format_loc(Loc), Ty])
            end;
        {type, _, map, any} -> {map_any};
        {type, _, map, Assocs} ->
            {map, lists:map(fun(A) -> trans_ty_map_assoc(Ctx, Env, A) end, Assocs)};
        {op, Anno, _, _, _} ->
            eval_const_ty(Ty, to_loc(Ctx, Anno));
        {op, Anno, _, _} ->
            eval_const_ty(Ty, to_loc(Ctx, Anno));
        {type, Anno, record, [{'atom', _, Name} | Fields]} ->
            Loc = to_loc(Ctx, Anno),
            Overrides =
                lists:map(
                    fun ({type, _, field_type, [{'atom', _, FieldName}, FieldTy]}) ->
                            {FieldName, trans_ty(Ctx, Env, FieldTy)}
                    end,
                    Fields),
            case maps:find(Name, Ctx#ctx.records) of
                error ->
                    errors:name_error(Loc, "record ~w not defined", [Name]);
                {ok, RecTy} ->
                    records:encode_record_ty(RecTy, Overrides)
            end;
        {type, _, tuple, any} -> {tuple_any};
        {type, _, tuple, ArgTys} -> {tuple, trans_tys(Ctx, Env, ArgTys)};
        {type, _, union, Tys} -> {union, trans_tys(Ctx, Env, Tys)};
        {var, Anno, Name} ->
            case Name of
                '_' -> {predef, any};
                _ -> {var, varenv:lookup(to_loc(Ctx, Anno), Name, Env)}
            end;
        {user_type, Anno, Name, ArgTys} ->
            % FIXME: should we check whether the reference is valid?
            Loc = to_loc(Ctx, Anno),
            Ref = {ty_ref, Ctx#ctx.module_name, Name, arity(Loc, ArgTys)},
            {named, Loc, Ref, trans_tys(Ctx, Env, ArgTys)};
        {remote_type, Anno, [{'atom', _, ety}, {'atom', _, Name}, ArgTys]} ->
            resolve_ety_ty(to_loc(Ctx, Anno), Name, trans_tys(Ctx, Env, ArgTys));
        {remote_type, Anno, [{'atom', _, Mod}, {'atom', _, Name}, ArgTys]} ->
            Loc = to_loc(Ctx, Anno),
            {named, Loc, {ty_qref, Mod, Name, arity(Loc, ArgTys)}, trans_tys(Ctx, Env, ArgTys)};
        {type, Anno, Name, ArgTys} ->
            Loc = to_loc(Ctx, Anno),
            NewArgTys = trans_tys(Ctx, Env, ArgTys),
            case {Name, NewArgTys} of
                % There is a long discussion about improper lists here:
                % https://github.com/josefs/Gradualizer/issues/110
                % To keep things simple, we do not distinguish between an improper list
                % and a maybe-improper list.
                {nonempty_list, [T]} -> {nonempty_list, T};
                {maybe_improper_list, [T1, T2]} -> {improper_list, T1, T2};
                {nonempty_maybe_improper_list, [T1, T2]} -> {nonempty_improper_list, T1, T2};
                {nonempty_improper_list, [T1, T2]} -> {nonempty_improper_list, T1, T2};
                {record, [{singleton, RecordName}]} when is_atom(RecordName) ->
                    {record, RecordName, []};
                _ ->
                    case {ast:is_predef_name(Name), NewArgTys} of
                        {true, []} -> {predef, Name};
                        {true, _} ->
                            errors:ty_error("~s: Invalid application of builtin type: ~w",
                                            [ast:format_loc(Loc), Ty]);
                        {false, _} ->
                            case {ast:is_predef_alias_name(Name), NewArgTys} of
                                {true, []} -> {predef_alias, Name};
                                {true, _} ->
                                    errors:ty_error("~s: Invalid application of builtin alias: ~w ",
                                                    [ast:format_loc(Loc), Ty]);
                                _ ->
                                    case {Name, NewArgTys} of
                                        {bool, []} -> {predef_alias, boolean};
                                        {dynamic, []} -> {predef, any}; % FIXME: for now (2023-08-14), we treat dynamic as any. This is wrong and must be fixed
                                        _ ->
                                            errors:bug("~s: Unhandled builtin type: ~w",
                                                       [ast:format_loc(Loc), Ty])
                                    end
                            end
                    end
            end;
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec trans_tys(ctx(), tyenv(), [ast_erl:ty()]) -> [ast:ty()].
trans_tys(Ctx, Env, Tys) -> lists:map(fun(T) -> trans_ty(Ctx, Env, T) end, Tys).

-spec trans_ty_map_assoc(ctx(), tyenv(), ast_erl:ty_map_assoc()) -> ast:ty_map_assoc().
trans_ty_map_assoc(Ctx, Env, Assoc) ->
    case Assoc of
        {type, _, map_field_assoc, [KeyTy, ValTy]} ->
            {map_field_opt, trans_ty(Ctx, Env, KeyTy), trans_ty(Ctx, Env, ValTy)};
        {type, _, map_field_exact, [KeyTy, ValTy]} ->
            {map_field_req, trans_ty(Ctx, Env, KeyTy), trans_ty(Ctx, Env, ValTy)};
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec thread_through_env(varenv_local:t(), [T], fun((varenv_local:t(), T) -> {U, varenv_local:t()}))
    -> {[U], varenv_local:t()}.
thread_through_env(InitEnv, [], _Fun) -> {[], InitEnv};
thread_through_env(InitEnv, L, Fun) ->
    {Rev, ResultEnv} =
        lists:foldl(
            fun(X, {L, Env}) ->
                {NewX, NewEnv} = Fun(Env, X),
                {[NewX | L], NewEnv}
            end, {[], InitEnv}, L),
    {lists:reverse(Rev), ResultEnv}.

-spec trans_guards(ctx(), varenv_local:t(), [ast_erl:guard()]) -> [ast:guard()].
trans_guards(Ctx, Env, Guards) ->
    {NewGuards, _} = thread_through_env(Env, Guards, fun(Env, G) -> trans_exps(Ctx, Env, G) end),
    NewGuards.

-spec trans_exps(ctx(), varenv_local:t(), [ast_erl:exp()]) -> {[ast:exp()], varenv_local:t()}.
%               (ctx(), varenv_local:t(), ast:guard()) -> {ast:guard(), varenv_local:t()}.
trans_exps(Ctx, Env, Es) ->
    thread_through_env(Env, Es, fun(Env, E) -> trans_exp(Ctx, Env, E) end).

-spec trans_exp_seq_noenv(ctx(), varenv_local:t(), [ast_erl:exp()]) -> [ast:exp()].
% dialyzer does not support overloaded type specs with overlapping domains.
%                      (ctx(), varenv_local:t(), [ast_erl:guard()]) -> [ast:guard()].
trans_exp_seq_noenv(Ctx, Env, Es) ->
    {NewEs, _} = trans_exp_seq(Ctx, Env, Es),
    NewEs.

% Removes match expression 'Pat = Exp' if the match expression is not the last expression in the
% list.
% 'Pat = Exp, Rest' becomes 'case Exp of Pat -> Rest'
-spec shallow_remove_match([ast_erl:exp()]) -> [ast_erl:exp()].
shallow_remove_match(Exps) ->
    lists:foldr(
      fun(E, AfterExps) ->
              case AfterExps of
                  [] -> [E];
                  _ ->
                      case E of
                          {match, Anno, Pat, Rhs} ->
                              Clause = {clause, Anno, [Pat], [], AfterExps},
                              [{'case', Anno, Rhs, [Clause]}]; % ast_erl:case_clause()
                          _ -> [E | AfterExps]
                      end
              end
      end, [], Exps).

% Transforms a sequence of expression. Also removes match expressions, except if the match
% expression comes last. This case is later handled by trans_exp.
-spec trans_exp_seq(ctx(), varenv_local:t(), [ast_erl:exp()]) -> {[ast:exp()], varenv_local:t()}.
%                  (ctx(), varenv_local:t(), ast:guard()) -> {ast:guard(), varenv_local:t()}.
trans_exp_seq(Ctx, Env, Es) ->
    thread_through_env(Env, shallow_remove_match(Es), fun(Env, E) -> trans_exp(Ctx, Env, E) end).


-spec trans_exp_noenv(ctx(), varenv_local:t(), ast_erl:exp()) -> ast:exp().
%                    (ctx(), varenv_local:t(), ast_erl:guard_test()) -> ast:guard_test().
trans_exp_noenv(Ctx, Env, Exp) ->
    {E, _} = trans_exp(Ctx, Env, Exp),
    E.

% Scoping rules in short (for details see http://icai.ektf.hu/pdf/ICAI2007-vol2-pp137-145.pdf)
% - Function clauses and list comprehension, open a new scope:
%   new variables created here do not escape this scope.
% - Variables in patterns of function arguments and generators of list comprehension
%   shadow existing variables.
% - Variables created in if, case and receive expressions can be used after the expression
%   provided the variable is created in each branch.
%   (Otherwise, the variable is considered 'unsafe').
% - Variables created in catch or try expressions cannot be used after the expression.
%
% There are several test cases test_files/ast_transform/scope_*.erl for these scoping rules.
%
% The following transformation of expressions assumes that the erlang compiler performs
% its sanity checks before the transformation runs.
-spec trans_exp(ctx(), varenv_local:t(), ast_erl:exp()) -> {ast:exp(), varenv_local:t()}.
%               (ctx(), varenv_local:t(), ast_erl:guard_test()) -> {ast:guard(), varenv_local:t()}.
trans_exp(Ctx, Env, Exp) ->
    case Exp of
        {'atom', Anno, X} -> {{'atom', to_loc(Ctx, Anno), X}, Env};
        {'char', Anno, X} -> {{'char', to_loc(Ctx, Anno), X}, Env};
        {'float', Anno, X} -> {{'float', to_loc(Ctx, Anno), X}, Env};
        {'integer', Anno, X} -> {{'integer', to_loc(Ctx, Anno), X}, Env};
        {'string', Anno, X} -> {{'string', to_loc(Ctx, Anno), X}, Env};
        {block, Anno, Exps} ->
            {NewExps, NewEnv} = trans_exp_seq(Ctx, Env, Exps),
            {{block, to_loc(Ctx, Anno), NewExps}, NewEnv};
        {'case', Anno, E, Clauses} ->
            {TransE, Env1} = trans_exp(Ctx, Env, E),
            {TransClauses, Env2} = trans_case_clauses(Ctx, Env1, Clauses),
            {{'case', to_loc(Ctx, Anno), TransE, TransClauses}, Env2};
        {'catch', Anno, E} ->
            % Keep old Env, it's a catch
            {{'catch', to_loc(Ctx, Anno), trans_exp_noenv(Ctx, Env, E)}, Env};
        {cons, Anno, E1, E2} ->
            {[NewE1, NewE2], NewEnv} = trans_exps(Ctx, Env, [E1, E2]),
            ?LOG_TRACE("cons, NewEnv=~w", NewEnv),
            {{cons, to_loc(Ctx, Anno), NewE1, NewE2}, NewEnv};
        {'fun', Anno, {function, Name, Arity}} ->
            % FIXME: should we check whether the reference is valid?
            {{fun_ref, to_loc(Ctx, Anno), {ref, Name, Arity}}, Env};
        {'fun', Anno, {function, {'atom', _, Mod}, {'atom', _, Name}, {'integer', _, Arity}}} ->
            {{fun_ref, to_loc(Ctx, Anno), {qref, Mod, Name, Arity}}, Env};
        {'fun', Anno, {function, ModE, NameE, ArityE}} ->
            {[NewModE, NewNameE, NewArityE], NewEnv} = trans_exps(Ctx, Env, [ModE, NameE, ArityE]),
            {{fun_ref_dyn, to_loc(Ctx, Anno), {qref_dyn, NewModE, NewNameE, NewArityE}}, NewEnv};
        {'fun', Anno, {clauses, FunClauses}} ->
            {{'fun', to_loc(Ctx, Anno), no_name, trans_fun_clauses(Ctx, Env, FunClauses)}, Env};
        {named_fun, Anno, Name, FunClauses} ->
            {NewName, NewEnv} = varenv_local:insert(Name, Env),
            {{'fun', to_loc(Ctx, Anno), {local_bind, NewName},
              trans_fun_clauses(Ctx, NewEnv, FunClauses)}, Env};
        {call, Anno, {'atom', AnnoName, FunName}, Args} -> % special case
            LocName = to_loc(Ctx, AnnoName),
            {NewArgs, NewEnv} = trans_exps(Ctx, Env, Args),
            ?LOG_TRACE("Env after args: ~w", NewEnv),
            Loc = to_loc(Ctx, Anno),
            {{call, Loc,
              {var, LocName, resolve_name(LocName, Ctx, Env, FunName, arity(Loc, Args))},
              NewArgs},
             NewEnv};
        {call, Anno, {remote, _, {'atom', _, Mod}, {'atom', AnnoFunName, Fun}}, Args} ->
            % special case
            % FIXME: should we check whether the reference is valid?
            LocName = to_loc(Ctx, AnnoFunName),
            {NewArgs, NewEnv} = trans_exps(Ctx, Env, Args),
            {{call, to_loc(Ctx, Anno),
                {var, LocName, {qref, Mod, Fun, length(Args)}},
                 NewArgs},
             NewEnv};
        {call, Anno, {remote, _, ModExp, FunExp}, Args} ->
            {[NewModExp, NewFunExp], Env1} = trans_exps(Ctx, Env, [ModExp, FunExp]),
            {NewArgs, NewEnv} = trans_exps(Ctx, Env1, Args),
            {{call_remote, to_loc(Ctx, Anno), NewModExp, NewFunExp, NewArgs}, NewEnv};
        {call, Anno, FunExp, Args} ->
            {NewFunExp, Env1} = trans_exp(Ctx, Env, FunExp),
            {NewArgs, NewEnv} = trans_exps(Ctx, Env1, Args),
            {{call, to_loc(Ctx, Anno), NewFunExp, NewArgs}, NewEnv};
        {'if', Anno, Clauses} ->
            {NewIfClauses, NewEnv} = trans_if_clauses(Ctx, Env, Clauses),
            {{'if', to_loc(Ctx, Anno), NewIfClauses}, NewEnv};
        {lc, Anno, E, Qualifiers} ->
            {NewQ, NewEnv} = trans_qualifiers(Ctx, Env, Qualifiers),
            % keep the old Env, list comprehension opens a new scope
            {{lc, to_loc(Ctx, Anno), trans_exp_noenv(Ctx, NewEnv, E), NewQ}, Env};
        {bc, Anno, E, Qualifiers} ->
            {NewQ, NewEnv} = trans_qualifiers(Ctx, Env, Qualifiers),
            % keep the old Env, comprehension opens a new scope
            {{bc, to_loc(Ctx, Anno), trans_exp_noenv(Ctx, NewEnv, E), NewQ}, Env};
        {mc, Anno, {map_field_assoc, Anno, K, V}, Qualifiers} ->
            {NewQ, NewEnv} = trans_qualifiers(Ctx, Env, Qualifiers),
            % keep the old Env, map comprehension opens a new scope
            NewK = trans_exp_noenv(Ctx, NewEnv, K),
            NewV = trans_exp_noenv(Ctx, NewEnv, V),
            {{mc, to_loc(Ctx, Anno), NewK, NewV, NewQ}, Env};
        {bin, Anno, Elems} ->
            {NewElems, NewEnv} =
                thread_through_env(Env, Elems, fun(Env, S) -> trans_exp_bin_elem(Ctx, Env, S) end),
            {{bin, to_loc(Ctx, Anno), NewElems}, NewEnv};
        {map, Anno, MapAssocs} ->
            {NewMapAssocs, NewEnv} = trans_map_assocs(Ctx, Env, MapAssocs),
            {{map_create, to_loc(Ctx, Anno), NewMapAssocs}, NewEnv};
        {map, Anno, E, MapAssocs} ->
            {NewE, Env1} = trans_exp(Ctx, Env, E),
            {NewMapAssocs, Env2} = trans_map_assocs(Ctx, Env1, MapAssocs),
            {{map_update, to_loc(Ctx, Anno), NewE, NewMapAssocs}, Env2};
        {match, Anno, Pat, E} ->
            % If a match expression appears as a single expression or as the last expression
            % in a sequence, than it is not removed by shallow_remove_match. In this case,
            % we rewrite it as a case here.
            {NewExp, E1} = trans_exp(Ctx, Env, E),
            {Q, E2} = trans_pat(Ctx, E1, Pat, bind_fresh),
            Loc = to_loc(Ctx, Anno),
            % The expression returned is 'case NewExp of ($X = Q) -> $x'
            % $X is not a valid erlang variable, so there is no danger of conflicting with
            % existing variables.
            {MatchVar, NewEnv} = varenv_local:insert_fresh(E2),
            % ast:case_clause()
            Clause = {case_clause, Loc,
                      {match, Loc, {var, Loc, {local_bind, MatchVar}}, Q},
                      [], % no guards
                      [{var, Loc, {local_ref, MatchVar}}]},
            {{'case', Loc, NewExp, [Clause]}, NewEnv}; %
        {nil, Anno} -> {{nil, to_loc(Ctx, Anno)}, Env};
        {op, Anno, Op, L, R} ->
            {[NewL, NewR], NewEnv} = trans_exps(Ctx, Env, [L, R]),
            {{op, to_loc(Ctx, Anno), Op, NewL, NewR}, NewEnv};
        {op, Anno, Op, E} ->
            {NewE, NewEnv} = trans_exp(Ctx, Env, E),
            {{op, to_loc(Ctx, Anno), Op, NewE}, NewEnv};
        {'receive', Anno, CaseClauses} ->
            {NewClauses, NewEnv} = trans_case_clauses(Ctx, Env, CaseClauses),
            {{'receive', to_loc(Ctx, Anno), NewClauses}, NewEnv};
        {'receive', Anno, CaseClauses, AfterExp, AfterBody} ->
            {NewAfterExp, Env1} = trans_exp(Ctx, Env, AfterExp),
            {NewCaseClauses, Env2} = trans_case_clauses(Ctx, Env1, CaseClauses),
            {NewAfterBody, Env3} = trans_exp_seq(Ctx, Env1, AfterBody),
            Env4 = varenv_local:merge_envs([Env2, Env3]),
            {{receive_after, to_loc(Ctx, Anno), NewCaseClauses,
                NewAfterExp, NewAfterBody}, Env4};
        {'record', Anno, Name, Fields} ->
            % record creation
            {NewFields, NewEnv} =
                thread_through_env(
                  Env,
                  Fields,
                  fun(Env, {record_field, Anno, F, FieldExp}) ->
                    {NewFieldExp, NewEnv} = trans_exp(Ctx, Env, FieldExp),
                    case F of
                        {'atom', _, FieldName} ->
                            {{record_field, to_loc(Ctx, Anno), FieldName, NewFieldExp}, NewEnv};
                        {'var', _, '_'} ->
                            {{record_field_other, to_loc(Ctx, Anno), NewFieldExp}, NewEnv}
                    end
                  end
                 ),
            {{record_create, to_loc(Ctx, Anno), Name, NewFields}, NewEnv};
        {record_field, Anno, E, Name, {'atom', _, Field}} ->
            {NewE, NewEnv} = trans_exp(Ctx, Env, E),
            % record field access
            {{record_field, to_loc(Ctx, Anno), NewE, Name, Field}, NewEnv};
        {record_index, Anno, Name, {'atom', _, Field}} ->
            % record index
            {{record_index, to_loc(Ctx, Anno), Name, Field}, Env};
        {'record', Anno, E, Name, Fields} ->
            % record update
            {NewE, Env1} = trans_exp(Ctx, Env, E),
            {NewFields, NewEnv} =
                thread_through_env(
                  Env1,
                  Fields,
                  fun(Env, {record_field, Anno, {'atom', _, FieldName}, FieldExp}) ->
                          {NewFieldExp, NewEnv} = trans_exp(Ctx, Env, FieldExp),
                          {{record_field, to_loc(Ctx, Anno), FieldName, NewFieldExp},
                           NewEnv}
                  end
                 ),
            {{record_update, to_loc(Ctx, Anno), NewE, Name, NewFields}, NewEnv};
        {tuple, Anno, Args} ->
            {NewArgs, NewEnv} = trans_exps(Ctx, Env, Args),
            {{tuple, to_loc(Ctx, Anno), NewArgs}, NewEnv};
        {'try', Anno, Body, CaseClauses, CatchClauses, AfterBody} ->
            {NewBody, Env1} = trans_exp_seq(Ctx, Env, Body),
            {NewCaseClauses, _} = trans_case_clauses(Ctx, Env1, CaseClauses),
            NewCatchClauses = trans_catch_clauses(Ctx, Env, CatchClauses),
            NewAfterBody = trans_exp_seq_noenv(Ctx, Env, AfterBody),
            {{'try', to_loc(Ctx, Anno), NewBody, NewCaseClauses, NewCatchClauses, NewAfterBody},
             Env};
        {var, Anno, Name} ->
            Loc = to_loc(Ctx, Anno),
            {{var, Loc, {local_ref, varenv_local:lookup(Loc, Name, Env)}}, Env};
        X -> errors:uncovered_case(?FILE, ?LINE, Ctx#ctx.path, X)
    end.

-spec trans_exp_bin_elem(ctx(), varenv_local:t(), ast_erl:exp_bitstring_elem()) ->
          {ast:exp_bitstring_elem(), varenv_local:t()}.
trans_exp_bin_elem(Ctx, Env, Elem) ->
    case Elem of
        {bin_element, Anno, ValExp, Size, Tyspecs} ->
            {NewValExp, Env1} = trans_exp(Ctx, Env, ValExp),
            {NewSize, Env2} =
                case Size of
                    default -> {default, Env1};
                    SizeExp -> trans_exp(Ctx, Env1, SizeExp)
                end,
            {{bin_element, to_loc(Ctx, Anno), NewValExp, NewSize, Tyspecs}, Env2}
    end.

% The given name might refer to (a) a local variable or (b) or global variable
% defined in the same module or (c) a global variable from a different module
% (such a variable must have been imported).
-spec resolve_name(ast:loc(), ctx(), varenv_local:t(), atom(), arity()) -> ast:any_ref().
resolve_name(Loc, Ctx, Env, Name, Ar) ->
    case varenv_local:find(Name, Env) of
        {ok, LocalName} -> {local_ref, LocalName};
        error ->
            case varenv:find({Name, Ar}, Ctx#ctx.funenv) of
                {ok, intern} -> {ref, Name, Ar};
                {ok, {extern, ModName}} -> {qref, ModName, Name, Ar};
                error -> errors:name_error(Loc, "undefined function ~s/~w", [Name, Ar])
            end
    end.

-spec trans_pats(ctx(), varenv_local:t(), [ast_erl:pat()], bind_mode()) ->
          {[ast:pat()], varenv_local:t()}.
trans_pats(Ctx, Env, Pats, BindMode) ->
    thread_through_env(Env, Pats, fun(Env, P) -> trans_pat(Ctx, Env, P, BindMode) end).

% - If BindMode is no_bind, then the pattern is not allowed to bind new variables
% - If BindMode is bind_fresh, then pattern variables create a reference to existing variables
%   and a new binding for unknown variables
% - If BindMode is shadow, then each pattern variables creates a new binding.
-type bind_mode() :: bind_fresh | no_bind | shadow.

-spec trans_pat
    (ctx(), varenv_local:t(), ast_erl:pat(), bind_mode()) -> {ast:pat(), varenv_local:t()}.
%    (ctx(), varenv_local:t(), ast_erl:exc_type_pat(), bind_mode()) ->
%    {ast:exc_type_pat(), varenv_local:t()}.
trans_pat(Ctx, Env, Pat, BindMode) ->
    case Pat of
        {'atom', Anno, X} -> {{'atom', to_loc(Ctx, Anno), X}, Env};
        {'char', Anno, X} -> {{'char', to_loc(Ctx, Anno), X}, Env};
        {'float', Anno, X} -> {{'float', to_loc(Ctx, Anno), X}, Env};
        {'integer', Anno, X} -> {{'integer', to_loc(Ctx, Anno), X}, Env};
        {'string', Anno, X} -> {{'string', to_loc(Ctx, Anno), X}, Env};
        {bin, Anno, Elems} ->
            {NewElems, NewEnv} =
                thread_through_env(Env, Elems,
                                   fun(Env, S) -> trans_pat_bin_elem(Ctx, Env, S, BindMode) end),
            {{bin, to_loc(Ctx, Anno), NewElems}, NewEnv};
        {match, Anno, P1, P2} ->
            {[Q1, Q2], NewEnv} = trans_pats(Ctx, Env, [P1, P2], BindMode),
            {{match, to_loc(Ctx, Anno), Q1, Q2}, NewEnv};
        {cons, Anno, P1, P2} ->
            {[Q1, Q2], NewEnv} = trans_pats(Ctx, Env, [P1, P2], BindMode),
            {{cons, to_loc(Ctx, Anno), Q1, Q2}, NewEnv};
        {nil, Anno} -> {{nil, to_loc(Ctx, Anno)}, Env};
        {map, Anno, Assocs} ->
            {NewAssocs, ResultEnv} =
                thread_through_env(Env, Assocs,
                    fun(E0, {map_field_exact, Anno, P1, P2}) ->
                        % the lhs of an assoc pattern P1 := P2 must not bind new vars
                        {Q1, E1} = trans_pat(Ctx, E0, P1, no_bind),
                        {Q2, E2} = trans_pat(Ctx, E1, P2, BindMode),
                        {{map_field_req, to_loc(Ctx, Anno), Q1, Q2}, E2}
                    end),
            {{map, to_loc(Ctx, Anno), NewAssocs}, ResultEnv};
        {op, Anno, Op, P1, P2} ->
            {Pats, NewEnv} = trans_pats(Ctx, Env, [P1, P2], BindMode),
            {{op, to_loc(Ctx, Anno), Op, Pats}, NewEnv};
        {op, Anno, Op, P} ->
            {Q, NewEnv} = trans_pat(Ctx, Env, P, BindMode),
            {{op, to_loc(Ctx, Anno), Op, [Q]}, NewEnv};
        {record, Anno, Name, Fields} ->
            {NewFields, NewEnv} =
                thread_through_env(
                  Env, Fields,
                  fun(E0, {record_field, Anno,  {'atom', _, FieldName}, FieldPat}) ->
                        {NewPat, E1} =
                            trans_pat(Ctx, E0, FieldPat, BindMode),
                                {{record_field, to_loc(Ctx, Anno), FieldName, NewPat}, E1}
                  end),
            {{record, to_loc(Ctx, Anno), Name, NewFields}, NewEnv};
        {record_index, Anno, RecName, {'atom', _, FieldName}} ->
            {{record_index, to_loc(Ctx, Anno), RecName, FieldName}, Env};
        {tuple, Anno, Pats} ->
            {NewPats, NewEnv} = trans_pats(Ctx, Env, Pats, BindMode),
            {{tuple, to_loc(Ctx, Anno), NewPats}, NewEnv};
        {var, Anno, '_'} ->
            {{wildcard, to_loc(Ctx, Anno)}, Env};
        {var, Anno, V} ->
            Loc = to_loc(Ctx, Anno),
            case BindMode of
                shadow ->
                    {Name, NewEnv} = varenv_local:insert(V, Env),
                    ?LOG_TRACE("Introducing new binding ~w at ~s", Name, ast:format_loc(Loc)),
                    {{var, Loc, {local_bind, Name}}, NewEnv};
                no_bind ->
                    case varenv_local:find(V , Env) of
                        {ok, Name} -> {{var, Loc, {local_ref, Name}}, Env};
                        error -> errors:name_error(Loc, "variable ~w is unbound", V)
                    end;
                bind_fresh ->
                    case varenv_local:find(V , Env) of
                        {ok, Name} -> {{var, Loc, {local_ref, Name}}, Env};
                        error ->
                            {Name, NewEnv} = varenv_local:insert(V, Env),
                            ?LOG_TRACE("Introducing new binding ~w at ~s", Name,
                                       ast:format_loc(Loc)),
                            {{var, Loc, {local_bind, Name}}, NewEnv}
                    end
            end;
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec trans_pat_bin_elem(ctx(), varenv_local:t(), ast_erl:pat_bitstring_elem(), bind_mode()) ->
          {ast:pat_bitstring_elem(), varenv_local:t()}.
trans_pat_bin_elem(Ctx, Env, Elem, BindMode) ->
    case Elem of
        {bin_element, Anno, ValPat, Size, Tyspecs} ->
            {NewValPat, Env1} = trans_pat(Ctx, Env, ValPat, BindMode),
            {NewSize, Env2} =
                case Size of
                    default -> {default, Env1};
                    SizeExp -> trans_exp(Ctx, Env1, SizeExp)
                end,
            {{bin_element, to_loc(Ctx, Anno), NewValPat, NewSize, Tyspecs}, Env2}
    end.

-spec trans_case_clauses(ctx(), varenv_local:t(), [ast_erl:case_clause()])
                        -> {[ast:case_clause()], varenv_local:t()}.
trans_case_clauses(_Ctx, Env, []) -> {[], Env};
trans_case_clauses(Ctx, Env, Cs) ->
    {NewClauses, NewEnvs} =
        lists:unzip(lists:map(fun(C) -> trans_case_clause(Ctx, Env, C) end, Cs)),
    ?LOG_TRACE("Merging envs: ~200p", NewEnvs),
    {NewClauses, varenv_local:merge_envs(NewEnvs)}.

-spec trans_case_clause(ctx(), varenv_local:t(), ast_erl:case_clause())
                       -> {ast:case_clause(), varenv_local:t()}.
trans_case_clause(Ctx, Env, C) ->
    case C of
        {clause, Anno, [Pat], Guards, Body} ->
            {Q, QEnv} = trans_pat(Ctx, Env, Pat, bind_fresh),
            NewGuards = trans_guards(Ctx, QEnv, Guards),
            Loc = to_loc(Ctx, Anno),
            ?LOG_TRACE("Env for body of case clause at ~s: ~w", ast:format_loc(Loc), QEnv),
            {NewBody, NewEnv} = trans_exp_seq(Ctx, QEnv, Body),
            {{case_clause, Loc, Q, NewGuards, NewBody}, NewEnv};
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec trans_catch_clauses(ctx(), varenv_local:t(),
                          [ast_erl:catch_clause()]) -> [ast:catch_clause()].
trans_catch_clauses(Ctx, Env, Cs) -> lists:map(fun(C) -> trans_catch_clause(Ctx, Env, C) end, Cs).

-spec trans_catch_clause(ctx(), varenv_local:t(), ast_erl:catch_clause()) -> ast:catch_clause().
trans_catch_clause(Ctx, Env, C) ->
    case C of
        {clause, Anno, [{tuple, _, L}], Guards, Body} ->
            {[X, P, S], NewEnv} = trans_pats(Ctx, Env, L, bind_fresh),
            case S of
                {var, StackLoc, {local_ref, {StackName, _}}} ->
                    errors:name_error(StackLoc,
                                      "stacktrace variable ~w must not be previously bound",
                                      StackName);
                _ -> ok
            end,
            NewGuards = trans_guards(Ctx, NewEnv, Guards),
            NewBody = trans_exp_seq_noenv(Ctx, NewEnv, Body),
            {catch_clause, to_loc(Ctx, Anno), X, P, S, NewGuards, NewBody};
        Z -> errors:uncovered_case(?FILE, ?LINE, Z)
    end.

-spec trans_fun_clauses(ctx(), [ast_erl:fun_clause()]) -> [ast:fun_clause()].
trans_fun_clauses(Ctx, Cs) -> trans_fun_clauses(Ctx, varenv_local:empty(), Cs).

-spec trans_fun_clauses(ctx(), varenv_local:t(), [ast_erl:fun_clause()]) -> [ast:fun_clause()].
trans_fun_clauses(Ctx, Env, Cs) -> lists:map(fun(C) -> trans_fun_clause(Ctx, Env, C) end, Cs).

-spec trans_fun_clause(ctx(), varenv_local:t(), ast_erl:fun_clause()) -> ast:fun_clause().
trans_fun_clause(Ctx, Env, C) ->
    case C of
        {clause, Anno, Ps, Guards, Body} ->
            {Qs, QEnv} = trans_pats(Ctx, Env, Ps, shadow),
            NewGuards = trans_guards(Ctx, QEnv, Guards),
            NewBody = trans_exp_seq_noenv(Ctx, QEnv, Body),
            {fun_clause, to_loc(Ctx, Anno), Qs, NewGuards, NewBody};
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec trans_if_clauses(ctx(), varenv_local:t(), [ast_erl:if_clause()])
                      -> {[ast:if_clause()], varenv_local:t()}.
trans_if_clauses(_Ctx, Env, []) -> {[], Env};
trans_if_clauses(Ctx, Env, Cs) ->
    {NewClauses, NewEnvs} =
        lists:unzip(lists:map(fun(C) -> trans_if_clause(Ctx, Env, C) end, Cs)),
    {NewClauses, varenv_local:merge_envs(NewEnvs)}.

-spec trans_if_clause(ctx(), varenv_local:t(), ast_erl:if_clause())
                     -> {ast:if_clause(), varenv_local:t()}.
trans_if_clause(Ctx, Env, C) ->
    case C of
        {clause, Anno, [], Guards, Body} ->
            NewGuards = trans_guards(Ctx, Env, Guards),
            {NewBody, NewEnv} = trans_exp_seq(Ctx, Env, Body),
            {{if_clause, to_loc(Ctx, Anno), NewGuards, NewBody}, NewEnv};
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec trans_qualifiers(ctx(), varenv_local:t(), [ast_erl:qualifier()])
    -> {[ast:qualifier()], varenv_local:t()}.
trans_qualifiers(Ctx, Env, Qs) ->
    thread_through_env(Env, Qs, fun(Env, Q) -> trans_qualifier(Ctx, Env, Q) end).

-spec trans_qualifier(ctx(), varenv_local:t(), ast_erl:qualifier())
    -> {ast:qualifier(), varenv_local:t()}.
trans_qualifier(Ctx, Env, Q) ->
    case Q of
        {K, Anno, Pat, Exp} when (K == generate orelse K == b_generate) -> % generator "Pat <- Exp"
            NewExp = trans_exp_noenv(Ctx, Env, Exp),
            {NewPat, NewEnv} = trans_pat(Ctx, Env, Pat, shadow),
            {{K, to_loc(Ctx, Anno), NewPat, NewExp}, NewEnv};
        {m_generate, Anno, {map_field_exact, _Anno2, K, V}, Exp} ->
            NewExp = trans_exp_noenv(Ctx, Env, Exp),
            {NewK, NewEnv1} = trans_pat(Ctx, Env, K, shadow),
            {NewV, NewEnv2} = trans_pat(Ctx, NewEnv1, V, shadow),
            {{m_generate, to_loc(Ctx, Anno), NewK, NewV, NewExp}, NewEnv2};
        Exp -> % filter
            trans_exp(Ctx, Env, Exp)
    end.

-spec trans_map_assocs(ctx(), varenv_local:t(), [ast_erl:map_assoc()])
                      -> {[ast:map_assoc()], varenv_local:t()}.
trans_map_assocs(Ctx, Env, As) ->
    thread_through_env(Env, As, fun(Env, A) -> trans_map_assoc(Ctx, Env, A) end).

-spec trans_map_assoc(ctx(), varenv_local:t(), ast_erl:map_assoc())
                     -> {ast:map_assoc(), varenv_local:t()}.
trans_map_assoc(Ctx, Env, Assoc) ->
    case Assoc of
        {K, Anno, ExpKey, ExpVal} when (K == map_field_assoc orelse K == map_field_exact) ->
            {NewExpKey, Env1} = trans_exp(Ctx, Env, ExpKey),
            {NewExpVal, Env2} = trans_exp(Ctx, Env1, ExpVal),
            NewK =
                case K of
                    map_field_assoc -> map_field_opt;
                    map_field_exact -> map_field_req
                end,
            {{NewK, to_loc(Ctx, Anno), NewExpKey, NewExpVal}, Env2};
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec trans_record_fields(ctx(), tyenv(), [ast_erl:record_field()]) -> [ast:record_field()].
trans_record_fields(Ctx, TyEnv, Fields) ->
    lists:map(fun (F) -> trans_record_field(Ctx, TyEnv, F) end, Fields).

-spec trans_record_field(ctx(), tyenv(), ast_erl:record_field()) -> ast:record_field().
trans_record_field(Ctx, TyEnv, Field) ->
    case Field of
        {typed_record_field, UntypedField, Ty} ->
            case trans_record_field(Ctx, TyEnv, UntypedField) of
                {record_field, Loc, Name, _, Def} ->
                    {record_field, Loc, Name, trans_ty(Ctx, TyEnv, Ty), Def}
            end;
        {record_field, Anno, {'atom', _, Name}} ->
            {record_field, to_loc(Ctx, Anno), Name, untyped, no_default};
        {record_field, Anno, {'atom', _, Name}, DefaultExp} ->
            {record_field, to_loc(Ctx, Anno), Name, untyped,
             trans_exp_noenv(Ctx, varenv_local:empty(), DefaultExp)};
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec arity(ast:loc(), [any()]) -> arity().
arity(Loc, L) ->
    Len = length(L),
    if Len < 256 -> Len;
       true -> errors:ty_error(Loc, "too many arguments: ~w", Len)
    end.
