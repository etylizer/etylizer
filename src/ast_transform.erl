-module(ast_transform).

-export([
    trans/2, trans/3, trans/4
]).

-export_type([trans_mode/0]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-etylizer({disable_exhaustiveness_toplevel, [eval_type_int/1]}).

-compile([nowarn_shadow_vars]).

-include("log.hrl").
-include("etylizer.hrl").

-record(ctx,
        { path :: file:filename(),
          module_name :: atom(),
          funenv :: funenv(),
          % The records seen so far. We need the record definitions to rewrite record types
          % into tuple types.
          records :: #{ atom() => records:record_ty() },
          % Default expressions for record fields, used to fill in omitted fields during
          % record construction.
          record_defaults = #{} :: #{ atom() => #{ atom() => ast:exp() } },
          % functions for which exhaustiveness has been added at the function clause level
          % via a -etylizer({disable_exhaustiveness_toplevel, [...]}) user-specified attribute
          % depends on annotations being transformed before function definitions
          nonexhaustive_funs = sets:new() :: sets:set({atom(), arity()}),
          % Extra type forms generated for record override variants (e.g., #rec{field :: any()})
          extra_forms = [] :: [ast:form()]
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
    {RevNewForms, FinalCtx} =
        lists:foldl(
            fun(F, {NewForms, Ctx}) ->
                case trans_form(Ctx, F, Mode) of
                    error -> {NewForms, Ctx};
                    {error, NewCtx} -> {NewForms, NewCtx};
                    {NewForm, NewCtx} -> {[NewForm | NewForms], NewCtx};
                    NewForm -> {[NewForm | NewForms], Ctx}
                end
            end,
            {[], #ctx{ path = Path, module_name = ModName, funenv = FunEnv, records = #{} }},
            Forms
            ),
    lists:reverse(RevNewForms) ++ FinalCtx#ctx.extra_forms.

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

-spec trans_form(ctx(), ast_erl:form(), trans_mode()) -> {ast:form(), ctx()} | ast:form() | error | {error, ctx()}.
trans_form(Ctx, Form, Mode) ->
    case Form of
        {attribute, Anno, export, X} -> {attribute, to_loc(Ctx, Anno), export, X};
        {attribute, Anno, export_type, X} -> {attribute, to_loc(Ctx, Anno), export_type, X};
        {attribute, Anno, import, X} -> {attribute, to_loc(Ctx, Anno), import, X};
        {attribute, Anno, module, X} -> {attribute, to_loc(Ctx, Anno), module, X};
        {attribute, Anno, compile, X} -> {attribute, to_loc(Ctx, Anno), compile, X};
        {attribute, _Anno, etylizer, {disable_exhaustiveness_toplevel, ListOfFuns}} ->
            % add functions where an exhaustive header are added in the transform phase
            {error, Ctx#ctx { nonexhaustive_funs = sets:union(Ctx#ctx.nonexhaustive_funs, sets:from_list(ListOfFuns)) }};
        {attribute, Anno, etylizer, {disable_exhaustiveness, ListOfFuns}} ->
            {attribute, to_loc(Ctx, Anno), etylizer, {disable_exhaustiveness, ListOfFuns}};
        {attribute, _, file, _} -> error;
        {attribute, _, behaviour, _} -> error;
        {attribute, _, behavior, _} -> error;
        {function, Anno, Name, Arity, Clauses} ->
            case Mode of
                full ->
                    DisableExhaustive = sets:is_element({Name, Arity}, Ctx#ctx.nonexhaustive_funs),
                    {function, to_loc(Ctx, Anno), Name, Arity, trans_fun_clauses(Ctx, Clauses, {DisableExhaustive, Arity})};
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
        {attribute, Anno, record, {Name, Fields}} when is_atom(Name) ->
            % We temporarily register the name of the record with an empty record
            % type, so that fields of the record can refer to the record itself.
            % Self-references in field types emit named references (see trans_ty).
            EmptyRecordTy = {Name, []},
            TmpCtx = Ctx#ctx { records = maps:put(Name, EmptyRecordTy, Ctx#ctx.records) },
            NewFields = trans_record_fields(TmpCtx, varenv:empty("type variable"), Fields),
            NewForm = {attribute, to_loc(TmpCtx, Anno), record, {Name, NewFields}},
            RecordTy = records:record_ty_from_decl(Name, NewFields),
            FieldDefaults = extract_field_defaults(NewFields),
            % Generate type forms for override variants created during field processing
            OverrideVariants = collect_record_variants(Name),
            Loc = to_loc(Ctx, Anno),
            VariantForms = lists:map(
                fun ({VariantName, VOverrides}) ->
                    VariantBody = records:encode_record_ty(RecordTy, VOverrides),
                    {attribute, Loc, type, transparent,
                        {VariantName, {ty_scheme, [], VariantBody}}}
                end,
                OverrideVariants),
            NewCtx = Ctx#ctx {
                records = maps:put(Name, RecordTy, Ctx#ctx.records),
                record_defaults = maps:put(Name, FieldDefaults, Ctx#ctx.record_defaults),
                extra_forms = Ctx#ctx.extra_forms ++ VariantForms
            },
            ?LOG_TRACE("Registered new record type: ~200p", RecordTy),
            {NewForm, NewCtx};
        {attribute, Anno, type, Def} ->
            {attribute, to_loc(Ctx, Anno), type, transparent, trans_tydef(Ctx, Def)};
        {attribute, Anno, opaque, Def} ->
            {attribute, to_loc(Ctx, Anno), type, opaque, trans_tydef(Ctx, Def)};
        {attribute, Anno, nominal, Def} ->
            {attribute, to_loc(Ctx, Anno), type, nominal, trans_tydef(Ctx, Def)};
        {attribute, Anno, Other, _} ->
            ?LOG_TRACE("Ignoring attribute ~w at ~s", Other, ast:format_loc(to_loc(Ctx, Anno))),
            error;
        {warning, _} -> error;
        {eof, _} -> error;
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec to_loc(ctx(), ast_erl:anno()) -> ast:loc().
to_loc(Ctx, Anno) -> ast:to_loc(Ctx#ctx.path, Anno).

-spec trans_spec_ty(ctx(), ast:loc(), [ast_erl:ty_full_fun()]) -> ast:ty_scheme().
trans_spec_ty(Ctx, Loc, FunTys) ->
    AllTyvars = % :: [ast_erl:ty_full_fun()]
        utils:everything(
          % TODO why is the guard not enough to narrow down the type to ast_erl:ty_var()?
          fun (V = {var, _, Name}) when is_atom(Name) -> {ok, ?assert_type(V, ast_erl:ty_var())};
              (_) -> error
          end,
          FunTys),
    {UnconstrFunTys, NestedConstrs} =
        lists:unzip(
          lists:map( % FIXME list2 not supported
            fun ({type, _Anno, bounded_fun, [Ty, Constrs]}) ->
                    {
                     ?assert_type(Ty, ast_erl:ty_fun_unconstrained_ty()),
                     ?assert_type(Constrs, ast_erl:ty_fun_constraint())
                    };
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

% support for etylizer:negation, etylizer:intersection, and etylizer:without
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
    errors:ty_error(L, "Invalid use of builtin type etylizer:~w", Name).

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

-spec eval_type_int(ast_erl:ty()) -> integer().
eval_type_int({integer, _, V}) -> V;
eval_type_int({op, _, '+', A, B}) -> eval_type_int(A) + eval_type_int(B);
eval_type_int({op, _, '-', A, B}) -> eval_type_int(A) - eval_type_int(B);
eval_type_int({op, _, '*', A, B}) -> eval_type_int(A) * eval_type_int(B);
eval_type_int({op, _, '-', A}) -> -eval_type_int(A).

-spec trans_ty(ctx(), tyenv(), ast_erl:ty()) -> ast:ty().
trans_ty(Ctx, Env, Ty) ->
    case Ty of
        {ann_type, _, [_, T]} -> trans_ty(Ctx, Env, T);
        {'atom', _, X} -> {singleton, X};
        {'char', _, X} -> {singleton, X};
        {'integer', _, X} -> {singleton, X};
        {type, _, binary, []} -> {bitstring, 0, 8};  % binary()
        {type, _, binary, [M, N]} ->
            MI = eval_type_int(M),
            NI = eval_type_int(N),
            {bitstring, MI, NI};
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
            case maps:find(Name, Ctx#ctx.records) of
                error ->
                    errors:name_error(Loc, "record ~w not defined", [Name]);
                {ok, RecTy} ->
                    case Fields of
                        [] ->
                            % Use named reference (enables recursive records)
                            RecRef = {ty_ref, Ctx#ctx.module_name, records:record_type_name(Name), 0},
                            {named, Loc, RecRef, []};
                        _ ->
                            Overrides =
                                lists:map(
                                    fun ({type, _, field_type, [{'atom', _, FieldName}, FieldTy]}) ->
                                            {FieldName, trans_ty(Ctx, Env, FieldTy)}
                                    end,
                                    Fields),
                            case RecTy of
                                {Name, []} ->
                                    % Self-referencing record with field overrides.
                                    % Emit a named reference to an override variant type.
                                    VariantName = store_record_variant(Name, Overrides),
                                    VariantRef = {ty_ref, Ctx#ctx.module_name, VariantName, 0},
                                    {named, Loc, VariantRef, []};
                                _ ->
                                    records:encode_record_ty(RecTy, Overrides)
                            end
                    end
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
        {remote_type, Anno, [{'atom', _, etylizer}, {'atom', _, Name}, ArgTys]} ->
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
                            errors:ty_error(Loc, "Invalid application of builtin type: ~w", Ty);
                        {false, _} ->
                            case {ast:is_predef_alias_name(Name), NewArgTys} of
                                {true, []} -> {predef_alias, Name};
                                {true, _} ->
                                    errors:ty_error(Loc, "Invalid application of builtin alias: ~w ", Ty);
                                _ ->
                                    case {Name, NewArgTys} of
                                        {bool, []} -> {predef_alias, boolean};
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
            {{'fun', to_loc(Ctx, Anno), no_name, trans_fun_clauses_no_exhaust(Ctx, Env, FunClauses)}, Env};
        {named_fun, Anno, Name, FunClauses} ->
            {NewName, NewEnv} = varenv_local:insert(Name, Env),
            {{'fun', to_loc(Ctx, Anno), {local_bind, NewName},
            trans_fun_clauses_no_exhaust(Ctx, NewEnv, FunClauses)}, Env};
        % annotate type
        {call, _, {'atom', _, '::'}, [Exp0, {string, Anno, TypeStr}]} -> 
            case parse_type(Ctx, TypeStr) of
                error -> errors:ty_error(to_loc(Ctx, Anno), "Invalid type annotation");
                {ok, TypeOfExp} -> 
                    {NewExp, NewEnv} = trans_exp(Ctx, Env, Exp0), 
                    {{annotate, to_loc(Ctx, Anno), NewExp, TypeOfExp}, NewEnv}
            end;
        % force type
        {call, _, {'atom', _, ':::'}, [Exp0, {string, Anno, TypeStr}]} -> 
            case parse_type(Ctx, TypeStr) of
                error -> errors:ty_error(to_loc(Ctx, Anno), "Invalid type assert");
                {ok, TypeOfExp} -> 
                    {NewExp, NewEnv} = trans_exp(Ctx, Env, Exp0), 
                    {{assert, to_loc(Ctx, Anno), NewExp, TypeOfExp}, NewEnv}
            end;
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
        {mc, Anno, {map_field_assoc, _Anno2, K, V}, Qualifiers} ->
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
        {'maybe', _Anno, _Exps} ->
            trans_maybe(Ctx, Env, Exp, none);
        {'maybe', Anno, Exps, Else = {'else', _ElseAnno, _Cs0}} ->
            trans_maybe(Ctx, Env, {'maybe', Anno, Exps}, Else);
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
            % fill in default expressions for omitted fields
            AllFields = fill_record_defaults(Ctx, Name, to_loc(Ctx, Anno), NewFields),
            {{record_create, to_loc(Ctx, Anno), Name, AllFields}, NewEnv};
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
            % transform try-of into try without an of section to simplify constraint generation
            RewrittenBody = case CaseClauses of
                [] -> Body; % no of section
                _ ->
                    {InitExprs, LastExpr} = case Body of
                        [] -> {[], {atom, Anno, undefined}}; % empty body edge case
                        [Single] -> {[], Single}; % single expression
                        _ -> {lists:droplast(Body), lists:last(Body)}
                    end,
                    CaseExp = {'case', Anno, LastExpr, CaseClauses},
                    % wrap in block: begin InitExprs..., case LastExpr of Clauses end end
                    [{block, Anno, InitExprs ++ [CaseExp]}]
            end,

            {TransformedBody, _UnusedEnv} = trans_exp_seq(Ctx, Env, RewrittenBody),
            % catch clauses use original Env  since try body vars are unsafe
            NewCatchClauses = trans_catch_clauses(Ctx, Env, CatchClauses),
            NewAfterBody = trans_exp_seq_noenv(Ctx, Env, AfterBody),
            % cases field is always empty after transformation
            {{'try', to_loc(Ctx, Anno), TransformedBody, [], NewCatchClauses, NewAfterBody},
             Env};
        {var, Anno, Name} ->
            Loc = to_loc(Ctx, Anno),
            {{var, Loc, {local_ref, varenv_local:lookup(Loc, Name, Env)}}, Env};
        X -> errors:uncovered_case(?FILE, ?LINE, Ctx#ctx.path, X)
    end.

-spec mk_maybe_expr
    (ast_erl:anno(), ast_erl:exps(), none) -> ast_erl:exp_maybe();
    (ast_erl:anno(), ast_erl:exps(), {'else', ast_erl:anno(), [ast_erl:maybe_else_clause()]}) -> ast_erl:exp_maybe_else().
mk_maybe_expr(A, M, none) -> {'maybe', A, M}; 
mk_maybe_expr(A, M, Else) -> {'maybe', A, M, Else}.

-spec trans_maybe(ctx(), varenv_local:t(), ast_erl:exp(), none | {'else', ast_erl:anno(), [ast_erl:maybe_else_clause()]}) -> {ast:exp(), varenv_local:t()}.
trans_maybe(Ctx, Env, {'maybe', Anno, [Exp]}, Else) -> 
    case Exp of
        {'maybe_match', L, P, E} ->
            case Else of
                none ->
                    % validate that P can match E's type, then return E
                    FreshVar = {var, L, '$maybe'},
                    SuccessClause = {clause, L, [{match, L, P, FreshVar}], [], [FreshVar]},
                    FailClause = {clause, L, [FreshVar], [], [FreshVar]},
                    Case = {'case', L, E, [SuccessClause, FailClause]},
                    trans_exp(Ctx, Env, Case);
                {'else', _ElseAnno, Cs0} ->
                    FreshVar = {var, Anno, '$maybe'},
                    SuccessClause = {clause, Anno, [{match, Anno, P, FreshVar}], [], [FreshVar]},
                    Case = {'case', Anno, E, [SuccessClause | Cs0]},
                    trans_exp(Ctx, Env, Case)
            end;
        _ ->
            case Else of
                none ->
                    trans_exp(Ctx, Env, Exp);
                {'else', _ElseAnno, Cs0} ->
                    % else clauses are semantically unreachable without ?=,
                    % but we keep them so the type checker sees all branches
                    SuccessClause = {clause, Anno, [{var, Anno, '_'}], [], [Exp]},
                    Case = {'case', Anno, Exp, [SuccessClause | Cs0]},
                    trans_exp(Ctx, Env, Case)
            end
    end;
trans_maybe(Ctx, Env, {'maybe', Anno, [Exp | Exps]}, Else) -> 
    case Exp of
        {'maybe_match', L, P, E} -> 
            % pattern matches -> continue with remaining Exps
            SuccessClause = {clause, L, [P], [], [mk_maybe_expr(Anno, Exps, Else)]},
            
            % pattern doesn't match -> return original E or do the else clauses
            FailClauses =
            case Else of
                % need to create a fresh variable to avoid binding variables by accident
                none ->
                    FreshVar = {var, L, '$maybe'},
                    [{clause, L, [FreshVar], [], [FreshVar]}];
                {'else', _ElseAnno, Cs0} -> Cs0
            end,
            NewExp = {'case', L, E, [SuccessClause | FailClauses]},
            trans_exp(Ctx, Env, NewExp);
        _ -> 
            NewExp = {block, Anno, [Exp, mk_maybe_expr(Anno, Exps, Else)]},
            % not a maybe match, then it's just a block
            trans_exp(Ctx, Env, NewExp)
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

-spec trans_fun_clauses(ctx(), [ast_erl:fun_clause()], {boolean(), arity()}) -> [ast:fun_clause()].
trans_fun_clauses(Ctx, Cs, DisableExhaustiveCtx) -> trans_fun_clauses(Ctx, varenv_local:empty(), Cs, DisableExhaustiveCtx).

-spec trans_fun_clauses_no_exhaust(ctx(), varenv_local:t(), [ast_erl:fun_clause()]) -> [ast:fun_clause()].
trans_fun_clauses_no_exhaust(Ctx, Env, Cs) -> 
    trans_fun_clauses(Ctx, Env, Cs, {false, 0}).

-spec trans_fun_clauses(ctx(), varenv_local:t(), [ast_erl:fun_clause()], {boolean(), arity()}) -> [ast:fun_clause()].
trans_fun_clauses(Ctx, Env, Cs, {DisableExhaustive, Arity}) ->
    Clauses = lists:map(fun(C) -> trans_fun_clause(Ctx, Env, C) end, Cs),

    FilteredClauses =  case Clauses of
        [_] -> Clauses;
        [_|_] ->
            {fun_clause, Loc, _, _, Body} = lists:nth(length(Clauses), Clauses),
            case is_error_clause(Body) of
                true ->
                    ?LOG_DEBUG("Exhaustiveness heuristic triggered: removing last error clause at ~p", Loc),
                    lists:sublist(Clauses, length(Clauses) - 1);
                false -> Clauses
            end
    end,

    % if this function is marked as not exhaustive,
    % we add a dummy function header to that clause
    % so that the type system does not complain
    AllClauses = case DisableExhaustive of
        true -> FilteredClauses ++ [add_exhaustive_clause(Ctx, Arity)];
        false -> FilteredClauses
    end,
    optimize_dispatched_clauses(AllClauses).



-spec trans_fun_clause(ctx(), varenv_local:t(), ast_erl:fun_clause()) -> ast:fun_clause().
trans_fun_clause(Ctx, Env, C) ->
    case C of
        {clause, Anno, Ps, Guards, Body} ->
            % shadow variables from outer context, 
            % but don't bind multiple variables inside this pattern
            % mode shadow and using Env does not work for X = ..., fun(X, X) -> ...
            % as it would create X1= ..., fun(X2, X3) -> ...
            % whereas it should be X1= ..., fun(X2, X2) -> ...
            % -> use a new local context with bind_fresh, 
            % but remember numbering of Variables in Env
            % merge afterwards, where QEnv0 takes precedence
            {Qs, QEnv0} = trans_pats(Ctx, varenv_local:empty(Env), Ps, bind_fresh),
            QEnv = varenv_local:merge(Env, QEnv0),
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
         % generator patterns for lists and bitstrings Pat <- / <:- / <= / <:= Exp
        {K, Anno, Pat, Exp} when 
              (K == generate orelse K == generate_strict orelse K == b_generate orelse K == b_generate_strict) ->
            NewExp = trans_exp_noenv(Ctx, Env, Exp),
            {NewPat, NewEnv} = trans_pat(Ctx, Env, Pat, shadow),
            {{K, to_loc(Ctx, Anno), NewPat, NewExp}, NewEnv};
         % map generate patterns  KeyPattern := ValuePattern <- / <:- MapExpression
        {K, Anno, {map_field_exact, _Anno2, KeyPat, ValPat}, Exp} when (K == m_generate orelse K == m_generate_strict)->
            NewExp = trans_exp_noenv(Ctx, Env, Exp),
            {NewK, NewEnv1} = trans_pat(Ctx, Env, KeyPat, shadow),
            {NewV, NewEnv2} = trans_pat(Ctx, NewEnv1, ValPat, shadow),
            {{K, to_loc(Ctx, Anno), NewK, NewV, NewExp}, NewEnv2};
        % zip generator
        {zip, Anno, Qs} -> 
            {NewQ, NewEnv} = trans_qualifiers(Ctx, Env, Qs),
            {{zip, to_loc(Ctx, Anno), NewQ}, NewEnv};
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

% Extracts default expressions from transformed record field declarations.
% Returns a map from field name to the default expression.
-spec extract_field_defaults([ast:record_field()]) -> #{ atom() => ast:exp() }.
extract_field_defaults(Fields) ->
    lists:foldl(
        fun({record_field, _Loc, _Name, _Ty, no_default}, Acc) -> Acc;
           ({record_field, _Loc, Name, _Ty, DefaultExp}, Acc) -> maps:put(Name, DefaultExp, Acc)
        end,
        #{},
        Fields).

% Fills in default expressions for record fields that are omitted during record creation.
% For each field in the record definition that is not explicitly given and has a default
% expression, a record_field entry with the default expression is appended.
-spec fill_record_defaults(ctx(), atom(), ast:loc(),
    [{record_field, ast:loc(), atom(), ast:exp()}]) ->
    [{record_field, ast:loc(), atom(), ast:exp()}].
fill_record_defaults(Ctx, RecName, Loc, GivenFields) ->
    case maps:find(RecName, Ctx#ctx.record_defaults) of
        error ->
            % Record not known yet (shouldn't happen for well-formed code)
            GivenFields;
        {ok, Defaults} ->
            GivenNames = sets:from_list(
                [N || {record_field, _, N, _} <- GivenFields],
                [{version, 2}]),
            DefaultFields =
                maps:fold(
                    fun(FieldName, DefaultExp, Acc) ->
                        case sets:is_element(FieldName, GivenNames) of
                            true -> Acc;
                            false -> [{record_field, Loc, FieldName, DefaultExp} | Acc]
                        end
                    end,
                    [],
                    Defaults),
            GivenFields ++ DefaultFields
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

% similar to what Gradualizer does
% ctx used for locations
-spec parse_type(ctx(), string()) -> error | {ok, ast:ty()}.
parse_type(Ctx, Src) ->
    AttrSrc = "-type t() :: " ++ Src ++ ".",
    {ok, Tokens, _EndLocation} = erl_scan:string(AttrSrc),
    % the variables in the outer function -type definition are not in scope in the annotation
    % at some point, we could extend this like Haskell's ScopeTypeVariables, if there is any need
    case erl_parse:parse_form(Tokens) of
        {ok, {attribute, _, type, Def = {t, _Type, []}}} ->
            {_, {ty_scheme, [], TyNew}} = trans_tydef(Ctx, Def),
            {ok, TyNew};
        _ -> error
    end.


-ifdef(TEST).

test_ctx() ->
    #ctx{ path = ".", module_name = ast_transform, funenv = varenv:empty("function"), records = #{} }.

parse_type_test() ->
    Ctx = test_ctx(),
    {ok, {predef_alias, string}} = parse_type(Ctx, "string()"),
    {ok, {singleton, a}} = parse_type(Ctx, "a"),

    % user types are supported (no locations, though)
    {ok, {named, _, _, [{named, _, _, _}]}} = parse_type(Ctx, "parser(command())"),

    % type error
    error = parse_type(Ctx, "not a type"),

    % free type variables not supported
    ?assertThrow({etylizer, name_error, _}, parse_type(Ctx, "A")),

    % type variables are only bound in the -spec annotation
    % therefore, no type variables are supported in annotations
    ?assertThrow({etylizer, name_error, _}, parse_type(Ctx, "fun((A) -> A)")),

    ok.

-endif.

% useful to check for erlang:error(_) function clauses
-spec is_error_clause([ast:exp()]) -> boolean().
is_error_clause(Body) ->
    case Body of
        [{'call', _, {var, _, {ref, error, 1}}, _}] -> true;
        [{'call', _, {var, _, {ref, error, 2}}, _}] -> true;
        [{'call', _, {var, _, {qref, erlang, error, 1}}, _}] -> true;
        [{'call', _, {var, _, {qref, erlang, error, 2}}, _}] -> true;
        _ -> false
    end.

% transform a function to be exhaustive by construction (user-specified flag)
-spec add_exhaustive_clause(ctx(), arity()) -> ast:fun_clause().
add_exhaustive_clause(Ctx, Arity) ->
    Loc = {loc, Ctx#ctx.path, 0, 0}, % dummy location TODO loc?
    ErrorCall = {'call', Loc, {var, Loc, {qref, erlang, error, 1}},
                [{'atom', Loc, exhaustive}]},
    {fun_clause, Loc, [{wildcard, Loc} || _ <- lists:seq(1, Arity)],
        [],
        [ErrorCall]}.

% Optimize multi-clause functions by removing non-dispatching arguments from case patterns.
% When some argument positions are always simple variables or wildcards across all clauses,
% rewrite into a single-clause function with a case expression on only the complex positions.
% E.g., f(ok, X, Y) -> ...; f(error, X, Y) -> ...
% becomes: f(Arg1, X, Y) -> case Arg1 of ok -> ...; error -> ... end
-spec optimize_dispatched_clauses([ast:fun_clause()]) -> [ast:fun_clause()].
optimize_dispatched_clauses(Clauses) when length(Clauses) < 2 -> Clauses;
optimize_dispatched_clauses(Clauses) ->
    [{fun_clause, _, FirstPats, _, _} | _] = Clauses,
    Arity = length(FirstPats),
    case Arity < 2 of
        true -> Clauses;
        false ->
            PositionTypes = classify_positions(Clauses, Arity),
            HasDirect = lists:any(fun(direct) -> true; (_) -> false end, PositionTypes),
            HasComplex = lists:any(fun(complex) -> true; (_) -> false end, PositionTypes),
            case {HasDirect, HasComplex} of
                {true, true} ->
                    case complex_has_catchall(Clauses, PositionTypes) of
                        true -> Clauses;
                        false ->
                            case guards_ref_direct_vars(Clauses, PositionTypes) of
                                true -> Clauses;
                                false -> rewrite_dispatched_clauses(Clauses, PositionTypes)
                            end
                    end;
                _ -> Clauses
            end
    end.

% Classify each argument position as 'direct' (always var/wildcard) or 'complex'.
-spec classify_positions([ast:fun_clause()], arity()) -> [direct | complex].
classify_positions(Clauses, Arity) ->
    lists:map(
        fun(I) ->
            AllSimple = lists:all(
                fun({fun_clause, _, Pats, _, _}) ->
                    case lists:nth(I, Pats) of
                        {var, _, {local_bind, _}} -> true;
                        {wildcard, _} -> true;
                        _ -> false
                    end
                end, Clauses),
            case AllSimple of
                true -> direct;
                false -> complex
            end
        end, lists:seq(1, Arity)).

% Check if any complex position has a catch-all pattern in some clause.
% A catch-all is a variable/wildcard, or a record pattern where all fields are catch-alls.
% This indicates intersection-type dispatch (e.g., tuple clause + catch-all clause),
% where converting to a case would make the catch-all branch appear redundant within
% one intersection component, causing a false "this branch never matches" error.
-spec complex_has_catchall([ast:fun_clause()], [direct | complex]) -> boolean().
complex_has_catchall(Clauses, PositionTypes) ->
    IndexedTypes = lists:zip(lists:seq(1, length(PositionTypes)), PositionTypes),
    lists:any(
        fun({I, complex}) ->
            lists:any(
                fun({fun_clause, _, Pats, _, _}) ->
                    pat_is_catchall(lists:nth(I, Pats))
                end, Clauses);
           ({_, direct}) -> false
        end, IndexedTypes).

-spec pat_is_catchall(ast:pat()) -> boolean().
pat_is_catchall({var, _, {local_bind, _}}) -> true;
pat_is_catchall({wildcard, _}) -> true;
pat_is_catchall({record, _, _, Fields}) ->
    lists:all(fun({record_field, _, _, Pat}) -> pat_is_catchall(Pat) end, Fields);
pat_is_catchall(_) -> false.

% Rewrite multi-clause function into single-clause with case on complex positions only.
-spec rewrite_dispatched_clauses([ast:fun_clause()], [direct | complex]) -> [ast:fun_clause()].
rewrite_dispatched_clauses(Clauses, PositionTypes) ->
    [{fun_clause, L, _, _, _} | _] = Clauses,
    Arity = length(PositionTypes),
    IndexedTypes = lists:zip(lists:seq(1, Arity), PositionTypes),
    ComplexIndices = [I || {I, complex} <- IndexedTypes],
    DirectIndices = [I || {I, direct} <- IndexedTypes],

    % Generate fresh variable names for all positions
    FreshVars = [begin
        Name = list_to_atom("$dispatch_" ++ integer_to_list(I)),
        {Name, erlang:unique_integer([positive])}
    end || I <- lists:seq(1, Arity)],

    % Build scrutiny from complex positions only
    ComplexVarRefs = [{var, L, {local_ref, lists:nth(I, FreshVars)}} || I <- ComplexIndices],
    ScrutExp = case ComplexVarRefs of
        [Single] -> Single;
        _ -> {tuple, L, ComplexVarRefs}
    end,

    % Build case clauses from original fun clauses
    CaseClauses = lists:map(
        fun({fun_clause, CL, Pats, Guards, Body}) ->
            % Case pattern from complex positions only
            ComplexPats = [lists:nth(I, Pats) || I <- ComplexIndices],
            CasePat = case ComplexPats of
                [SinglePat] -> SinglePat;
                _ -> {tuple, CL, ComplexPats}
            end,

            % Build substitution map: original direct-position vars -> fresh vars
            SubstMap = lists:foldl(
                fun(I, Acc) ->
                    SharedVar = lists:nth(I, FreshVars),
                    case lists:nth(I, Pats) of
                        {var, _, {local_bind, V}} when V =/= SharedVar ->
                            Acc#{V => SharedVar};
                        _ -> Acc % wildcard or already matches
                    end
                end, #{}, DirectIndices),

            NewGuards = subst_local_refs(Guards, SubstMap),
            NewBody = subst_local_refs(Body, SubstMap),
            {case_clause, CL, CasePat, NewGuards, NewBody}
        end, Clauses),

    % Build outer single fun clause
    OuterPats = [{var, L, {local_bind, V}} || V <- FreshVars],
    CaseExp = {'case', L, ScrutExp, CaseClauses},
    [{fun_clause, L, OuterPats, [], [CaseExp]}].

% Substitute local variable references in AST terms.
% Replaces {local_ref, V} with {local_ref, NewV} where V is in SubstMap.
-spec subst_local_refs(term(), #{ast:local_varname() => ast:local_varname()}) -> term().
subst_local_refs(Term, SubstMap) when map_size(SubstMap) == 0 -> Term;
subst_local_refs({local_ref, V} = Term, SubstMap) ->
    case maps:find(V, SubstMap) of
        {ok, NewV} -> {local_ref, NewV};
        error -> Term
    end;
subst_local_refs(T, SubstMap) when is_tuple(T) ->
    list_to_tuple(subst_local_refs_list(tuple_to_list(T), SubstMap));
subst_local_refs([H|T], SubstMap) ->
    [subst_local_refs(H, SubstMap) | subst_local_refs(T, SubstMap)];
subst_local_refs(Term, _) -> Term.

-spec subst_local_refs_list([term()], #{ast:local_varname() => ast:local_varname()}) -> [term()].
subst_local_refs_list([], _) -> [];
subst_local_refs_list([H|T], SubstMap) ->
    [subst_local_refs(H, SubstMap) | subst_local_refs_list(T, SubstMap)].

% Check if any guard in any clause references a variable from a direct position.
% When guards reference direct-position variables, the optimization cannot be applied
% because the guard variables would no longer be bound by the case pattern, breaking
% the lower-bound computation in pat_guard_lower_upper (exhaustiveness analysis).
-spec guards_ref_direct_vars([ast:fun_clause()], [direct | complex]) -> boolean().
guards_ref_direct_vars(Clauses, PositionTypes) ->
    DirectIndices = [I || {I, direct} <- lists:zip(lists:seq(1, length(PositionTypes)), PositionTypes)],
    lists:any(
        fun({fun_clause, _, Pats, Guards, _}) ->
            case Guards of
                [] -> false;
                _ ->
                    DirectVars = sets:from_list(
                        lists:filtermap(
                            fun(I) ->
                                case lists:nth(I, Pats) of
                                    {var, _, {local_bind, V}} -> {true, V};
                                    _ -> false
                                end
                            end, DirectIndices),
                        [{version, 2}]),
                    has_local_ref(Guards, DirectVars)
            end
        end, Clauses).

% Walk an AST term and check if it contains any {local_ref, V} where V is in VarSet.
-spec has_local_ref(term(), sets:set(ast:local_varname())) -> boolean().
has_local_ref({local_ref, V}, VarSet) -> sets:is_element(V, VarSet);
has_local_ref(T, VarSet) when is_tuple(T) ->
    has_local_ref_list(tuple_to_list(T), VarSet);
has_local_ref([H|T], VarSet) ->
    has_local_ref(H, VarSet) orelse has_local_ref(T, VarSet);
has_local_ref(_, _) -> false.

-spec has_local_ref_list([term()], sets:set(ast:local_varname())) -> boolean().
has_local_ref_list([], _) -> false;
has_local_ref_list([H|T], VarSet) ->
    has_local_ref(H, VarSet) orelse has_local_ref_list(T, VarSet).

% Stores a record override variant in the process dictionary for later retrieval.
% Used when a self-referencing record has field overrides (e.g., #rr{name :: any()}).
% Returns the generated variant type name.
-spec store_record_variant(atom(), [records:record_field()]) -> atom().
store_record_variant(RecName, Overrides) ->
    ListKey = {etylizer_record_variants, RecName},
    Existing = case get(ListKey) of undefined -> []; L -> L end,
    N = length(Existing) + 1,
    VariantName = list_to_atom("$record$" ++ atom_to_list(RecName) ++ "$v" ++ integer_to_list(N)),
    put(ListKey, [{VariantName, Overrides} | Existing]),
    VariantName.

% Collects and removes all record override variants from the process dictionary.
-spec collect_record_variants(atom()) -> [{atom(), [records:record_field()]}].
collect_record_variants(RecName) ->
    ListKey = {etylizer_record_variants, RecName},
    case erase(ListKey) of
        undefined -> [];
        Variants -> Variants
    end.
