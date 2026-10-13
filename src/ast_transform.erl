-module(ast_transform).

-export([
    trans/2, trans/3, trans/4
]).

-export_type([trans_mode/0]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-export([spec_tyvars/1]).
-endif.


-compile([nowarn_shadow_vars]).

-include("log.hrl").
-include("etylizer.hrl").

-record(ctx,
        { path :: file:filename(),
          % starts equal to path, but updates on -include boundaries
          % useful to map locs back to include files
          % needed to make locs unique
          current_file :: file:filename(),
          module_name :: atom(),
          funenv :: funenv(),
          % The records seen so far. We need the record definitions to rewrite record types
          % into tuple types.
          records :: #{ atom() => ety_records:record_ty() },
          % Default expressions of record fields as in the source, with the file defining
          % the record. Erlang copies a default into each record construction that omits
          % the field, so it is translated there.
          record_defaults = #{} :: #{ atom() => {file:filename(), #{ atom() => ast_erl:exp() }} },
          % Extra type forms generated for record override variants (e.g., #rec{field :: any()})
          extra_forms = [] :: [ast:form()],
          % ETS table for accumulating record override variants during type transformation.
          % Used because trans_ty cannot thread state through its return value.
          record_variants :: ets:table() | undefined,
          % #414 enclosing maybe information when ?= does not match
          % result or the argument of the function
          maybe_else = none :: none | ast:exp()
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
    VarTab = ets:new(record_variants, [bag]),
    {RevNewForms, FinalCtx} =
        lists:foldl(
            fun(F, {NewForms, Ctx0}) ->
                Ctx = update_current_file(Ctx0, F),
                case trans_form(Ctx, F, Mode) of
                    error -> {NewForms, Ctx};
                    {NewForm, NewCtx} -> {[NewForm | NewForms], NewCtx};
                    NewForm -> {[NewForm | NewForms], Ctx}
                end
            end,
            {[], #ctx{ path = Path, current_file = Path, module_name = ModName,
                        funenv = FunEnv, records = #{},
                        record_variants = VarTab }},
            Forms
            ),
    ets:delete(VarTab),
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

-spec trans_form(ctx(), ast_erl:form(), trans_mode()) -> {ast:form(), ctx()} | ast:form() | error.
trans_form(Ctx, Form, Mode) ->
    R =
        case Form of
            {attribute, Anno, export, X} -> {attribute, to_loc(Ctx, Anno), export, X};
            {attribute, Anno, export_type, X} -> {attribute, to_loc(Ctx, Anno), export_type, X};
            {attribute, Anno, import, X} -> {attribute, to_loc(Ctx, Anno), import, X};
            {attribute, Anno, module, X} -> {attribute, to_loc(Ctx, Anno), module, X};
            {attribute, Anno, compile, X} -> {attribute, to_loc(Ctx, Anno), compile, X};
            {attribute, Anno, etylizer, EtylizerOpt} ->
                Loc = to_loc(Ctx, Anno),
                case trans_etylizer_opt(Ctx, Loc, EtylizerOpt) of
                    {ok, Opt} -> {attribute, Loc, etylizer, Opt};
                    error -> error
                end;
            {attribute, _, file, _} -> error;
            {attribute, _, behaviour, _} -> error;
            {attribute, _, behavior, _} -> error;
            {function, Anno, Name, Arity, Clauses} ->
                case Mode of
                    full ->
                        Loc = to_loc(Ctx, Anno),
                        {Args, Body} = trans_fun_clauses(Ctx, varenv_local:empty(), Clauses),
                        {function, Loc, Name, Arity, Args, Body};
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
                RecordTy = ety_records:record_ty_from_decl(Name, NewFields),
                FieldDefaults = {Ctx#ctx.current_file, extract_field_defaults(Fields)},
                % Generate type forms for override variants created during field processing
                OverrideVariants = collect_record_variants(Ctx, Name),
                Loc = to_loc(Ctx, Anno),
                VariantForms = lists:map(
                    fun ({VariantName, VOverrides}) ->
                        VariantBody = ety_records:encode_record_ty(RecordTy, VOverrides),
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
        end,
    R.

% The option of an -etylizer attribute, which is any term as the user has written it.
-spec trans_etylizer_opt(ctx(), ast:loc(), term()) -> {ok, ast:etylizer_opt()} | error.
trans_etylizer_opt(_Ctx, _Loc, Opt) ->
    case Opt of
        {Kind, off} when Kind =:= functions_exhaustive; Kind =:= functions_redundant ->
            {ok, {Kind, off}};
        {Kind, off, Funs} when Kind =:= functions_exhaustive; Kind =:= functions_redundant ->
            % the term of the attribute: a list of name/arity pairs
            {ok, {Kind, off, ?assert_type(Funs, [ast:fun_with_arity()])}};
        _ ->
            error
    end.

-spec to_loc(ctx(), ast_erl:anno()) -> ast:loc().
to_loc(Ctx, Anno) -> ast:to_loc(Ctx#ctx.current_file, Anno).

% Updates ctx.current_file when a top-level -file marker (inserted by epp at
% include boundaries) is encountered. 
% The module's own marker is mapped back to the original Path 
% so module locs keep their exact file string.
% Only header code switches to the header's path, 
% which is what makes header loc()s distinct from same-numbered module lines.
-spec update_current_file(ctx(), ast_erl:form()) -> ctx().
update_current_file(Ctx, {attribute, _, file, {MarkerFile, _}}) ->
    SameAsModule =
        filename:rootname(filename:basename(MarkerFile)) =:=
            filename:rootname(filename:basename(Ctx#ctx.path)),
    NewFile = case SameAsModule of true -> Ctx#ctx.path; false -> MarkerFile end,
    Ctx#ctx{ current_file = NewFile };
update_current_file(Ctx, _Form) -> Ctx.

-spec trans_spec_ty(ctx(), ast:loc(), [ast_erl:ty_full_fun()]) -> ast:ty_scheme().
trans_spec_ty(Ctx, Loc, FunTys) ->
    AllTyvars = spec_tyvars(FunTys),
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
    TyVars = lists:uniq([V || {var, _, V} <- AllTyvars]),
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

% All type variables of a spec, in the order in which they appear. This includes the
% names of annotated types (Name :: T) and the variables of constraints.
-spec spec_tyvars([ast_erl:ty_full_fun()]) -> [ast_erl:ty_var()].
spec_tyvars(FunTys) ->
    utils:everything(
      fun erl_ty_children/1,
      fun (V = {var, _, _}) -> {ok, V};
          (_) -> error
      end,
      FunTys).

% The direct subtypes of a type of the Erlang AST.
% Annotations are opaque, they are passed over and never looked into.
-spec erl_ty_children(external_types:erl_ty_node()) -> [external_types:erl_ty_node()].
erl_ty_children({var, _, _}) -> [];
erl_ty_children({atom, _, _}) -> [];
erl_ty_children({integer, _, _}) -> [];
erl_ty_children({char, _, _}) -> [];
erl_ty_children({op, _, _, A}) -> [A];
erl_ty_children({op, _, _, A, B}) -> [A, B];
erl_ty_children({ann_type, _, Args}) -> Args;
erl_ty_children({user_type, _, _, Args}) -> Args;
erl_ty_children({remote_type, _, Args}) -> lists:flatmap(fun erl_ty_arg/1, Args);
erl_ty_children({type, _, _, any}) -> [];
erl_ty_children({type, _, _, Args}) -> lists:flatmap(fun erl_ty_arg/1, Args).

-spec erl_ty_arg(external_types:erl_ty_arg()) -> [external_types:erl_ty_node()].
erl_ty_arg(L) when is_list(L) -> L;
erl_ty_arg({type, _, any}) -> [];
erl_ty_arg(T) -> [T].

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
            {subty_constraint, to_loc(Ctx, Anno), Name, trans_ty(Ctx, Env, Ty)}
    end.

% support for etylizer:negation, etylizer:intersection, etylizer:without, and etylizer:cons
-spec resolve_ety_ty(ast:loc(), atom(), [ast:ty()]) -> ast:ty().
resolve_ety_ty(_, negation, [Ty]) -> {negation, Ty};
resolve_ety_ty(_, intersection, Tys) ->
    case Tys of
        [] -> {predef, any};
        [Ty] -> Ty;
        _ -> {intersection, Tys}
    end;
resolve_ety_ty(_, without, [T, U]) -> {intersection, [T, {negation, U}]};
% a list cell: etylizer:cons(T, etylizer:cons(U, [])) is the type of the lists [X, Y]
% with X :: T and Y :: U
resolve_ety_ty(_, cons, [Hd, Tl]) -> {cons, Hd, Tl};
resolve_ety_ty(L, mu, [Body]) ->
    Name = mu_name(L),
    {mu, {mu_var, Name}, replace_mu_var(Body, Name)};
resolve_ety_ty(_, mu_var, []) -> {mu_var, '$mu_placeholder'};
resolve_ety_ty(L, Name, _) ->
    errors:ty_error(L, "Invalid use of builtin type etylizer:~w", Name).

-spec mu_name(ast:loc()) -> atom().
mu_name(Loc) ->
    {loc, File, Line, Col} = ?assert_pattern({loc, _, _, _}, ast:source_loc(Loc)),
    list_to_atom(lists:flatten(
        io_lib:format("$mu_~s_~p_~p_~p", [filename:basename(File), Line, Col, erlang:phash2(File)]))).

% The placeholder that etylizer:mu_var() leaves becomes the variable of the enclosing mu.
-spec replace_mu_var(ast:ty(), atom()) -> ast:ty().
replace_mu_var(Ty, Name) ->
    ast_traverse:ty_everywhere(
        fun({mu_var, '$mu_placeholder'}) -> {ok, {mu_var, Name}};
           (_) -> error
        end, Ty).

-spec eval_const_ty(ast_erl:ty_binop() | ast_erl:ty_unop(), ast:loc()) -> {singleton, integer()}.
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
        {type, _, binary, []} -> {bitstring, 0, 8};  % binary()
        {type, _, binary, [M, N]} ->
            case {M, N} of
                {{integer, _, MI}, {integer, _, NI}} when MI >= 0, NI >= 0 -> {bitstring, MI, NI};
                % PRECISION we could evaluate the expressions when they are constant
                %   2026-10-23 albsch
                _ -> {bitstring}
            end;
        {type, _, nil, []} -> {empty_list};
        {type, _, list, [T]} -> {list, trans_ty(Ctx, Env, T)};
        {type, _, 'fun', []} -> {fun_simple};
        {type, _, 'fun', [{type, _, any}, T]} -> {fun_any_arg, trans_ty(Ctx, Env, T)};
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
                    errors:ty_error(Loc, "Invalid range type: ~w", [Ty])
            end;
        {type, _, map, any} -> {map_any};
        {type, _, map, Assocs} when is_list(Assocs) ->
            {map, lists:map(fun(A) -> trans_ty_map_assoc(Ctx, Env, A) end, Assocs)};
        {op, Anno, _, _, _} ->
            eval_const_ty(Ty, to_loc(Ctx, Anno));
        {op, Anno, _, _} ->
            eval_const_ty(Ty, to_loc(Ctx, Anno));
        {type, _Anno, record, []} -> {tuple_any};
        {type, Anno, record, [{'atom', _, Name} | Fields]} ->
            Loc = to_loc(Ctx, Anno),
            case maps:find(Name, Ctx#ctx.records) of
                error ->
                    errors:name_error(Loc, "record ~w not defined", [Name]);
                {ok, RecTy} ->
                    case Fields of
                        [] ->
                            % Use named reference (enables recursive records)
                            RecRef = {ty_ref, Ctx#ctx.module_name, ety_records:record_type_name(Name), 0},
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
                                    VariantName = store_record_variant(Ctx, Name, Overrides),
                                    VariantRef = {ty_ref, Ctx#ctx.module_name, VariantName, 0},
                                    {named, Loc, VariantRef, []};
                                _ ->
                                    ety_records:encode_record_ty(RecTy, Overrides)
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
                % we follow the semantics of Erlang:
                % list_to_binary([2 | <<1>>])  -> <<2,1>>     % <<1>> termination OK
                % list_to_binary(<<1>>)        -> badarg      % <<1>> top level: ERROR
                % iolist_to_binary(<<1>>)      -> <<1>>
                % A maybe_improper_list(T1, T2) is [] or a cons chain over T1
                % whose final tail is in T2
                % nonempty_maybe_improper_list and nonempty_improper_list:
                % they differ only in their termination types
                {nonempty_list, [T]} -> {nonempty_list, T};
                {maybe_improper_list, [T1, T2]} ->
                    {union, [{empty_list}, {nonempty_improper_list, T1, T2}]};
                {nonempty_maybe_improper_list, [T1, T2]} -> {nonempty_improper_list, T1, T2};
                {nonempty_improper_list, [T1, T2]} -> {nonempty_improper_list, T1, T2};
                _ ->
                    case {ast:predef_name(Name), NewArgTys} of
                        {{ok, Predef}, []} -> {predef, Predef};
                        {{ok, _}, _} ->
                            errors:ty_error(Loc, "Invalid application of builtin type: ~w", Ty);
                        {error, _} ->
                            case {ast:predef_alias_name(Name), NewArgTys} of
                                {{ok, Alias}, []} -> {predef_alias, Alias};
                                {{ok, _}, _} ->
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
            end
    end.

-spec trans_tys(ctx(), tyenv(), [ast_erl:ty()]) -> [ast:ty()].
trans_tys(Ctx, Env, Tys) -> lists:map(fun(T) -> trans_ty(Ctx, Env, T) end, Tys).

-spec trans_ty_map_assoc(ctx(), tyenv(), ast_erl:ty_map_assoc()) -> ast:ty_map_assoc().
trans_ty_map_assoc(Ctx, Env, Assoc) ->
    case Assoc of
        {type, _, map_field_assoc, [KeyTy, ValTy]} ->
            {map_field_opt, trans_ty(Ctx, Env, KeyTy), trans_ty(Ctx, Env, ValTy)};
        {type, _, map_field_exact, [KeyTy, ValTy]} ->
            {map_field_req, trans_ty(Ctx, Env, KeyTy), trans_ty(Ctx, Env, ValTy)}
    end.

% A non-empty list stays non-empty.
-spec thread_through_env
    (varenv_local:t(), [T, ...], fun((varenv_local:t(), T) -> {U, varenv_local:t()})) -> {[U, ...], varenv_local:t()};
    (varenv_local:t(), [T], fun((varenv_local:t(), T) -> {U, varenv_local:t()})) -> {[U], varenv_local:t()}.
thread_through_env(InitEnv, [], _Fun) -> {[], InitEnv};
thread_through_env(InitEnv, [X | Xs], Fun) ->
    {NewX, Env} = Fun(InitEnv, X),
    {NewXs, ResultEnv} = thread_through_env(Env, Xs, Fun),
    {[NewX | NewXs], ResultEnv}.

-spec trans_guards(ctx(), varenv_local:t(), [ast_erl:guard()]) -> [ast:guard()].
trans_guards(Ctx, Env, Guards) ->
    {NewGuards, _} = thread_through_env(Env, Guards, fun(Env, G) -> trans_exps(Ctx, Env, G) end),
    NewGuards.

-spec trans_exps
    (ctx(), varenv_local:t(), [ast_erl:exp(), ...]) -> {[ast:exp(), ...], varenv_local:t()};
    (ctx(), varenv_local:t(), [ast_erl:exp()]) -> {[ast:exp()], varenv_local:t()}.
trans_exps(Ctx, Env, Es) ->
    thread_through_env(Env, Es, fun(Env, E) -> trans_exp(Ctx, Env, E) end).

-spec trans_exp_seq_noenv(ctx(), varenv_local:t(), ast_erl:exps()) -> ast:exps().
trans_exp_seq_noenv(Ctx, Env, Es) ->
    {NewEs, _} = trans_exp_seq(Ctx, Env, Es),
    NewEs.

% Transforms a sequence of expressions.
% A match at statement position nests the rest of the sequence:
% `Pat = Exp, Rest` becomes `case Exp of Pat -> Rest end`.
% A trailing match, or a match in operand/subexpression position,
% is left to trans_exp, which compiles it to a standalone single-clause case.
-spec trans_exp_seq(ctx(), varenv_local:t(), ast_erl:exps()) -> {ast:exps(), varenv_local:t()}.
trans_exp_seq(Ctx, Env, Es) ->
    trans_exp_seq(Ctx, Env, Es, fun(E, LastEnv) -> trans_exp(Ctx, LastEnv, E) end).

% Like trans_exp_seq/3, but the last expression of the sequence is transformed by Last.
-spec trans_exp_seq(ctx(), varenv_local:t(), ast_erl:exps(),
                    fun((ast_erl:exp(), varenv_local:t()) -> {ast:exp(), varenv_local:t()}))
                   -> {ast:exps(), varenv_local:t()}.
trans_exp_seq(_Ctx, Env, [E], Last) ->
    {NewE, NewEnv} = Last(E, Env),
    {[NewE], NewEnv};
trans_exp_seq(Ctx, Env, [{match, Anno, Pat, Rhs} | Rest], Last) ->
    L = to_loc(Ctx, Anno),
    G = ast:generated(match, L),
    Clause = generated_clause(Ctx, L, Pat, fun(QEnv) -> trans_exp_seq(Ctx, QEnv, Rest, Last) end),
    {Case, NewEnv} = trans_generated_case(Ctx, Env, G, Rhs, [Clause]),
    {[Case], NewEnv};
trans_exp_seq(Ctx, Env, [{maybe_match, Anno, Pat, Rhs} | Rest], Last) ->
    L = to_loc(Ctx, Anno),
    G = ast:generated('maybe', L),
    Clause = generated_clause(Ctx, L, Pat, fun(QEnv) -> trans_exp_seq(Ctx, QEnv, Rest, Last) end),
    {Case, NewEnv} = trans_generated_case(Ctx, Env, G, Rhs, [Clause, fresh_clause(Ctx, G)]),
    {[Case], NewEnv};
trans_exp_seq(Ctx, Env, [E | Rest], Last) ->
    {NewE, Env1} = trans_exp(Ctx, Env, E),
    {NewRest, NewEnv} = trans_exp_seq(Ctx, Env1, Rest, Last),
    {[NewE | NewRest], NewEnv}.


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
            {TransClauses, Env2, _PatEnv} = trans_case_clauses(Ctx, Env1, Clauses),
            % Variables bound in all branches become available to subsequent
            % expressions through the scope-lowering post-pass, not annotations.
            Loc = to_loc(Ctx, Anno),
            {{'case', Loc, TransE, TransClauses}, Env2};
        {'catch', Anno, E} ->
            % Keep old Env, it's a catch
            {{'catch', to_loc(Ctx, Anno), trans_exp_noenv(Ctx, Env, E)}, Env};
        {cons, Anno, E1, E2} ->
            {NewE1, Env1} = trans_exp(Ctx, Env, E1),
            {NewE2, NewEnv} = trans_exp(Ctx, Env1, E2),
            ?LOG_TRACE("cons, NewEnv=~w", NewEnv),
            {{cons, to_loc(Ctx, Anno), NewE1, NewE2}, NewEnv};
        {'fun', Anno, {function, Name, Arity}} ->
            % FIXME: should we check whether the reference is valid?
            {{fun_ref, to_loc(Ctx, Anno), {ref, Name, Arity}}, Env};
        {'fun', Anno, {function, {'atom', _, Mod}, {'atom', _, Name}, {'integer', _, Arity}}} ->
            {{fun_ref, to_loc(Ctx, Anno), {qref, Mod, Name, Arity}}, Env};
        {'fun', Anno, {function, ModE, NameE, ArityE}} ->
            {NewModE, Env1} = trans_exp(Ctx, Env, ModE),
            {NewNameE, Env2} = trans_exp(Ctx, Env1, NameE),
            {NewArityE, NewEnv} = trans_exp(Ctx, Env2, ArityE),
            {{fun_ref_dyn, to_loc(Ctx, Anno), {qref_dyn, NewModE, NewNameE, NewArityE}}, NewEnv};
        {'fun', Anno, {clauses, FunClauses}} ->
            Loc = to_loc(Ctx, Anno),
            {Args, Body} = trans_fun_clauses(Ctx, Env, FunClauses),
            {{'fun', Loc, no_name, Args, Body}, Env};
        {named_fun, Anno, Name, FunClauses} ->
            Loc = to_loc(Ctx, Anno),
            {NewName, NewEnv} = varenv_local:insert(Name, Env),
            {Args, Body} = trans_fun_clauses(Ctx, NewEnv, FunClauses),
            {{'fun', Loc, {local_bind, NewName}, Args, Body}, Env};
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
            {NewModExp, Env0} = trans_exp(Ctx, Env, ModExp),
            {NewFunExp, Env1} = trans_exp(Ctx, Env0, FunExp),
            {NewArgs, NewEnv} = trans_exps(Ctx, Env1, Args),
            {{call_remote, to_loc(Ctx, Anno), NewModExp, NewFunExp, NewArgs}, NewEnv};
        {call, Anno, FunExp, Args} ->
            {NewFunExp, Env1} = trans_exp(Ctx, Env, FunExp),
            {NewArgs, NewEnv} = trans_exps(Ctx, Env1, Args),
            {{call, to_loc(Ctx, Anno), NewFunExp, NewArgs}, NewEnv};
        {'if', Anno, Clauses} ->
            G = ast:generated('if', to_loc(Ctx, Anno)),
            Vars = if_guard_vars(Ctx, Env, Clauses),
            {NewClauses, NewEnv} = trans_if_clauses(Ctx, Env, Vars, Clauses),
            {{'case', G, {tuple, G, [{var, G, {local_ref, V}} || V <- Vars]}, NewClauses}, NewEnv};
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
            % Rewrite match as a case expression. Pattern variables 
            % are available to subsequent expressions
            Loc = to_loc(Ctx, Anno),
            G = ast:generated(match, Loc),
            trans_generated_case(Ctx, Env, G, E, [match_clause(Ctx, Loc, G, Pat)]);
        {maybe_match, Anno, Pat, E} ->
            Loc = to_loc(Ctx, Anno),
            G = ast:generated('maybe', Loc),
            trans_generated_case(Ctx, Env, G, E, [match_clause(Ctx, Loc, G, Pat), fresh_clause(Ctx, G)]);
        {nil, Anno} -> {{nil, to_loc(Ctx, Anno)}, Env};
        {op, Anno, Op, L, R} ->
            {NewL, Env1} = trans_exp(Ctx, Env, L),
            {NewR, NewEnv} = trans_exp(Ctx, Env1, R),
            {{op, to_loc(Ctx, Anno), Op, NewL, NewR}, NewEnv};
        {op, Anno, Op, E} ->
            {NewE, NewEnv} = trans_exp(Ctx, Env, E),
            {{op, to_loc(Ctx, Anno), Op, NewE}, NewEnv};
        {'maybe', Anno, Exps} ->
            trans_maybe(Ctx, Env, Anno, Exps, none);
        {'maybe', Anno, Exps, Else} ->
            trans_maybe(Ctx, Env, Anno, Exps, Else);
        {'receive', Anno, CaseClauses} ->
            {NewClauses, NewEnv, _PatEnv} = trans_case_clauses(Ctx, Env, CaseClauses),
            {{'receive', to_loc(Ctx, Anno), NewClauses}, NewEnv};
        {'receive', Anno, CaseClauses, AfterExp, AfterBody} ->
            {NewAfterExp, Env1} = trans_exp(Ctx, Env, AfterExp),
            {NewCaseClauses, Env2, _PatEnv2} = trans_case_clauses(Ctx, Env1, CaseClauses),
            {NewAfterBody, Env3} = trans_exp_seq(Ctx, Env1, AfterBody),
            Env4 = varenv_local:merge_envs([Env2, Env3]),
            {{receive_after, to_loc(Ctx, Anno), NewCaseClauses,
                NewAfterExp, NewAfterBody}, Env4};
        {'record', Anno, Name, Fields} ->
            % record creation
            Loc = to_loc(Ctx, Anno),
            RecTy = lookup_record(Ctx, Loc, Name),
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
            % expand _ = Expr into individual fields, then fill in defaults for the rest
            ExpandedFields = expand_record_field_other(RecTy, NewFields),
            AllFields = fill_record_defaults(Ctx, NewEnv, RecTy, Loc, ExpandedFields),
            {record_tuple(Loc, RecTy, AllFields), NewEnv};
        {record_field, Anno, E, Name, {'atom', _, Field}} ->
            {NewE, NewEnv} = trans_exp(Ctx, Env, E),
            % record field access
            {record_read(Ctx, to_loc(Ctx, Anno), Name, Field, NewE), NewEnv};
        {record_index, Anno, Name, {'atom', _, Field}} ->
            {trans_record_index(Ctx, to_loc(Ctx, Anno), Name, Field), Env};
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
            {trans_record_update(Ctx, NewEnv, to_loc(Ctx, Anno), NewE, Name, NewFields), NewEnv};
        {tuple, Anno, Args} ->
            {NewArgs, NewEnv} = trans_exps(Ctx, Env, Args),
            {{tuple, to_loc(Ctx, Anno), NewArgs}, NewEnv};
        {'try', Anno, Body, CaseClauses, CatchClauses, AfterBody} ->
            % transform try-of into try without an of section to simplify constraint generation:
            % try Init, Last of Clauses becomes try begin Init, case Last of Clauses end end
            TransformedBody = case CaseClauses of
                [] -> trans_exp_seq_noenv(Ctx, Env, Body); % no of section
                _ ->
                    G = ast:generated(try_of, to_loc(Ctx, Anno)),
                    {NewBody, _} = trans_exp_seq(Ctx, Env, Body,
                        fun(Last, LastEnv) -> trans_generated_case(Ctx, LastEnv, G, Last, CaseClauses) end),
                    [{block, G, NewBody}]
            end,

            % catch clauses use original Env since try body vars are unsafe
            NewCatchClauses = trans_catch_clauses(Ctx, Env, CatchClauses),
            % the only sequence that may be empty: a try without an after section
            NewAfterBody = case AfterBody of
                [] -> [];
                [_ | _] -> trans_exp_seq_noenv(Ctx, Env, AfterBody)
            end,
            % cases field is always empty after transformation
            {{'try', to_loc(Ctx, Anno), TransformedBody, [], NewCatchClauses, NewAfterBody},
             Env};
        {var, Anno, Name} ->
            Loc = to_loc(Ctx, Anno),
            Ref = case varenv_local:find_ref(Name, Env) of
                {ok, R} -> R;
                error ->
                    ?LOG_NOTE("Undefined local variable ~w at ~s", Name, ast:format_loc(Loc)),
                    errors:name_error(Loc, "Undefined local variable ~w", Name)
            end,
            {{var, Loc, Ref}, Env}
    end.

% result is either the value ?= does not match or the last value
% else clauses are one fun
% (fun(F) -> Exps end)(fun(X) -> case X of Clauses end end)
-spec trans_maybe(ctx(), varenv_local:t(), ast_erl:anno(), ast_erl:exps(),
                  none | {'else', ast_erl:anno(), [ast_erl:maybe_else_clause(), ...]})
                 -> {ast:exp(), varenv_local:t()}.
trans_maybe(Ctx, Env, Anno, Exps, none) ->
    {NewExps, NewEnv} = trans_exp_seq(Ctx#ctx{maybe_else = none}, Env, Exps),
    {{block, ast:generated('maybe', to_loc(Ctx, Anno)), NewExps}, NewEnv};
trans_maybe(Ctx, Env, Anno, Exps, {'else', ElseAnno, Clauses}) ->
    G = ast:generated('maybe', to_loc(Ctx, Anno)),
    GElse = ast:generated('maybe', to_loc(Ctx, ElseAnno)),
    {F, FEnv} = varenv_local:insert_fresh(Env),
    {X, XEnv} = varenv_local:insert_fresh(FEnv),
    {NewClauses, _, _} = trans_case_clauses(Ctx, XEnv, Clauses),
    {Body, _} = trans_exp_seq(Ctx#ctx{maybe_else = {var, G, {local_ref, F}}}, XEnv, Exps),
    ElseFun = generated_fun(G, X, [{'case', GElse, {var, GElse, {local_ref, X}}, NewClauses}]),
    {{call, G, generated_fun(G, F, Body), [ElseFun]}, Env}.

-spec generated_fun(ast:loc(), ast:local_varname(), ast:exps()) -> ast:exp().
generated_fun(G, V, Body) ->
    {'fun', G, no_name, [V], Body}.

% A case generated by a rewrite, at location G. Its clauses are clauses of the source,
% or generated clauses, which are built in the environment after the scrutinee.
-spec trans_generated_case(ctx(), varenv_local:t(), ast:loc(), ast_erl:exp(),
                           [ast_erl:case_clause() | generated_clause(), ...]) -> {ast:exp(), varenv_local:t()}.
trans_generated_case(Ctx, Env, G, Scrut, Clauses) ->
    {NewScrut, Env1} = trans_exp(Ctx, Env, Scrut),
    Results = lists:map(fun(C) when is_function(C) -> C(Env1);
                           (C) -> trans_case_clause(Ctx, Env1, C)
                        end, Clauses),
    {NewClauses, BodyEnvs, _} = lists:unzip3(Results),
    {{'case', G, NewScrut, NewClauses}, varenv_local:merge_envs(BodyEnvs)}.

-type generated_clause() ::
    fun((varenv_local:t()) -> {ast:case_clause(), varenv_local:t(), varenv_local:t()}).

% Pat -> Body at L, for a pattern of the source. Body is transformed in the environment after Pat
-spec generated_clause(ctx(), ast:loc(), ast_erl:pat(),
                       fun((varenv_local:t()) -> {ast:exps(), varenv_local:t()})) -> generated_clause().
generated_clause(Ctx, L, Pat, Body) ->
    fun(CaseEnv) ->
        {Q, QEnv} = trans_pat(Ctx, CaseEnv, Pat, bind_fresh),
        {NewBody, BodyEnv} = Body(QEnv),
        {{case_clause, L, Q, [], NewBody}, BodyEnv, QEnv}
    end.

% Fresh = Pat -> Fresh at L, for a pattern of the source and a fresh variable
-spec match_clause(ctx(), ast:loc(), ast:loc(), ast_erl:pat()) -> generated_clause().
match_clause(Ctx, L, G, Pat) ->
    fun(CaseEnv) ->
        {Q, QEnv} = trans_pat(Ctx, CaseEnv, Pat, bind_fresh),
        {V, VEnv} = varenv_local:insert_fresh(QEnv),
        {{case_clause, L, {match, G, {var, G, {local_bind, V}}, Q}, [], [{var, G, {local_ref, V}}]},
         VEnv, VEnv}
    end.

% Fresh -> Fresh for a fresh variable
% or Fresh -> ElseClauses(Fresh) for maybe
-spec fresh_clause(ctx(), ast:loc()) -> generated_clause().
fresh_clause(Ctx, G) ->
    fun(CaseEnv) ->
        {V, VEnv} = varenv_local:insert_fresh(CaseEnv),
        Ref = {var, G, {local_ref, V}},
        Body =
            case Ctx#ctx.maybe_else of
                none -> Ref;
                F -> {call, G, F, [Ref]}
            end,
        {{case_clause, G, {var, G, {local_bind, V}}, [], [Body]}, VEnv, VEnv}
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
    case varenv_local:find_ref(Name, Env) of
        {ok, Ref} -> Ref;
        error ->
            case varenv:find({Name, Ar}, Ctx#ctx.funenv) of
                {ok, intern} -> {ref, Name, Ar};
                {ok, {extern, ModName}} -> {qref, ModName, Name, Ar};
                error -> errors:name_error(Loc, "undefined function ~s/~w", [Name, Ar])
            end
    end.

-spec trans_pats(ctx(), varenv_local:t(), varenv_local:t(), [ast_erl:pat()], bind_mode()) ->
          {[ast:pat()], varenv_local:t()}.
trans_pats(Ctx, Outer, Env, Pats, BindMode) ->
    thread_through_env(Env, Pats, fun(Env, P) -> trans_pat(Ctx, Outer, Env, P, BindMode) end).

% - If BindMode is no_bind, then the pattern is not allowed to bind new variables
% - If BindMode is bind_fresh, then pattern variables create a reference to existing variables
%   and a new binding for unknown variables
% - If BindMode is shadow, then each pattern variables creates a new binding.
-type bind_mode() :: bind_fresh | no_bind | shadow.

-spec trans_pat
    (ctx(), varenv_local:t(), ast_erl:pat(), bind_mode()) -> {ast:pat(), varenv_local:t()}.
%    (ctx(), varenv_local:t(), ast_erl:exc_type_pat(), bind_mode()) ->
%    {ast:exc_type_pat(), varenv_local:t()}.
trans_pat(Ctx, Env, Pat, BindMode) -> trans_pat(Ctx, Env, Env, Pat, BindMode).

% Outer is the scope enclosing the whole pattern. Map keys and segment sizes are
% evaluated there, even if the pattern shadows one of their variables.
-spec trans_pat(ctx(), varenv_local:t(), varenv_local:t(), ast_erl:pat(), bind_mode()) ->
          {ast:pat(), varenv_local:t()}.
trans_pat(Ctx, Outer, Env, Pat, BindMode) ->
    case Pat of
        {'atom', Anno, X} -> {{'atom', to_loc(Ctx, Anno), X}, Env};
        {'char', Anno, X} -> {{'char', to_loc(Ctx, Anno), X}, Env};
        {'float', Anno, X} -> {{'float', to_loc(Ctx, Anno), X}, Env};
        {'integer', Anno, X} -> {{'integer', to_loc(Ctx, Anno), X}, Env};
        {'string', Anno, X} -> {{'string', to_loc(Ctx, Anno), X}, Env};
        {bin, Anno, Elems} ->
            % a size also sees the variables of the segments before it
            {NewElems, {NewEnv, _}} =
                lists:mapfoldl(
                  fun(S, {E, SizeEnv}) -> trans_pat_bin_elem(Ctx, SizeEnv, E, S, BindMode) end,
                  {Env, Outer}, Elems),
            {{bin, to_loc(Ctx, Anno), NewElems}, NewEnv};
        {match, Anno, P1, P2} ->
            {Q1, Env1} = trans_pat(Ctx, Outer, Env, P1, BindMode),
            {Q2, NewEnv} = trans_pat(Ctx, Outer, Env1, P2, BindMode),
            {{match, to_loc(Ctx, Anno), Q1, Q2}, NewEnv};
        {cons, Anno, P1, P2} ->
            {Q1, Env1} = trans_pat(Ctx, Outer, Env, P1, BindMode),
            {Q2, NewEnv} = trans_pat(Ctx, Outer, Env1, P2, BindMode),
            {{cons, to_loc(Ctx, Anno), Q1, Q2}, NewEnv};
        {nil, Anno} -> {{nil, to_loc(Ctx, Anno)}, Env};
        {map, Anno, Assocs} ->
            {NewAssocs, ResultEnv} =
                thread_through_env(Env, Assocs,
                    fun(E0, {map_field_exact, Anno, P1, P2}) ->
                        % the lhs of an assoc pattern P1 := P2 must not bind new vars
                        {Q1, _} = trans_pat(Ctx, Outer, P1, no_bind),
                        {Q2, E1} = trans_pat(Ctx, Outer, E0, P2, BindMode),
                        {{map_field_req, to_loc(Ctx, Anno), Q1, Q2}, E1}
                    end),
            {{map, to_loc(Ctx, Anno), NewAssocs}, ResultEnv};
        {op, Anno, Op, P1, P2} ->
            {Pats, NewEnv} = trans_pats(Ctx, Outer, Env, [P1, P2], BindMode),
            {{op, to_loc(Ctx, Anno), Op, Pats}, NewEnv};
        {op, Anno, Op, P} ->
            {Q, NewEnv} = trans_pat(Ctx, Outer, Env, P, BindMode),
            {{op, to_loc(Ctx, Anno), Op, [Q]}, NewEnv};
        {record, Anno, Name, Fields} ->
            {NewFields, NewEnv} =
                thread_through_env(
                  Env, Fields,
                  fun(E0, {record_field, Anno,  {'atom', _, FieldName}, FieldPat}) ->
                        {NewPat, E1} =
                            trans_pat(Ctx, Outer, E0, FieldPat, BindMode),
                                {{record_field, to_loc(Ctx, Anno), FieldName, NewPat}, E1}
                  end),
            Loc = to_loc(Ctx, Anno),
            RecTy = {_, DefFields} = lookup_record(Ctx, Loc, Name),
            G = ast:generated(record_field, Loc),
            Others = [{record_field, G, N, {wildcard, G}} || {N, _} <- DefFields],
            {record_tuple(Loc, RecTy, NewFields ++ Others), NewEnv};
        {record_index, Anno, RecName, {'atom', _, FieldName}} ->
            {trans_record_index(Ctx, to_loc(Ctx, Anno), RecName, FieldName), Env};
        {tuple, Anno, Pats} ->
            {NewPats, NewEnv} = trans_pats(Ctx, Outer, Env, Pats, BindMode),
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
            end
    end.

% The size is evaluated in SizeEnv, which then gets the variable of the segment.
-spec trans_pat_bin_elem(ctx(), varenv_local:t(), varenv_local:t(),
                         ast_erl:pat_bitstring_elem(), bind_mode()) ->
          {ast:pat_bitstring_elem(), {varenv_local:t(), varenv_local:t()}}.
trans_pat_bin_elem(Ctx, SizeEnv, Env, Elem, BindMode) ->
    case Elem of
        {bin_element, Anno, ValPat, Size, Tyspecs} ->
            {NewValPat, NewEnv} = trans_pat(Ctx, SizeEnv, Env, ValPat, BindMode),
            NewSize =
                case Size of
                    default -> default;
                    SizeExp -> trans_exp_noenv(Ctx, SizeEnv, SizeExp)
                end,
            NewSizeEnv =
                case NewValPat of
                    {var, _, {_, V}} -> varenv_local:insert_var(V, SizeEnv);
                    _ -> SizeEnv
                end,
            {{bin_element, to_loc(Ctx, Anno), NewValPat, NewSize, Tyspecs}, {NewEnv, NewSizeEnv}}
    end.

-spec trans_case_clauses
    (ctx(), varenv_local:t(), [ast_erl:case_clause(), ...])
        -> {[ast:case_clause(), ...], varenv_local:t(), varenv_local:t()};
    (ctx(), varenv_local:t(), [ast_erl:case_clause()])
        -> {[ast:case_clause()], varenv_local:t(), varenv_local:t()}.
trans_case_clauses(_Ctx, Env, []) -> {[], Env, Env};
trans_case_clauses(Ctx, Env, Cs) ->
    Results = lists:map(fun(C) -> trans_case_clause(Ctx, Env, C) end, Cs),
    {NewClauses, BodyEnvs, PatEnvs} = lists:unzip3(Results),
    ?LOG_TRACE("Merging envs: ~200p", BodyEnvs),
    {NewClauses, varenv_local:merge_envs(BodyEnvs), varenv_local:merge_envs(PatEnvs)}.

-spec trans_case_clause(ctx(), varenv_local:t(), ast_erl:case_clause())
                       -> {ast:case_clause(), varenv_local:t(), varenv_local:t()}.
trans_case_clause(Ctx, Env, C) ->
    case C of
        {clause, Anno, [Pat], Guards, Body} ->
            {Q, QEnv} = trans_pat(Ctx, Env, Pat, bind_fresh),
            NewGuards = trans_guards(Ctx, QEnv, Guards),
            Loc = to_loc(Ctx, Anno),
            ?LOG_TRACE("Env for body of case clause at ~s: ~w", ast:format_loc(Loc), QEnv),
            {NewBody, NewEnv} = trans_exp_seq(Ctx, QEnv, Body),
            {{case_clause, Loc, Q, NewGuards, NewBody}, NewEnv, QEnv}
    end.

-spec trans_catch_clauses(ctx(), varenv_local:t(),
                          [ast_erl:catch_clause()]) -> [ast:catch_clause()].
trans_catch_clauses(Ctx, Env, Cs) -> lists:map(fun(C) -> trans_catch_clause(Ctx, Env, C) end, Cs).

-spec trans_catch_clause(ctx(), varenv_local:t(), ast_erl:catch_clause()) -> ast:catch_clause().
trans_catch_clause(Ctx, Env, {clause, Anno, [{tuple, _, [ClassPat, ValuePat, StackPat]}], Guards, Body}) ->
    {X, Env1} = trans_pat(Ctx, Env, ClassPat, bind_fresh),
    {P, Env2} = trans_pat(Ctx, Env1, ValuePat, bind_fresh),
    {S, NewEnv} = trans_pat(Ctx, Env2, StackPat, bind_fresh),
    case S of
        {var, StackLoc, {local_ref, {StackName, _}}} ->
            errors:name_error(StackLoc,
                              "stacktrace variable ~w must not be previously bound",
                              StackName);
        _ -> ok
    end,
    NewGuards = trans_guards(Ctx, NewEnv, Guards),
    NewBody = trans_exp_seq_noenv(Ctx, NewEnv, Body),
    {catch_clause, to_loc(Ctx, Anno), exc_type_pat(X), P, stacktrace_pat(S), NewGuards, NewBody}.

% The class of a catch clause is an atom, a variable or _, and its stacktrace a variable or _.
% trans_pat/4 gives a pattern of any kind.
-spec exc_type_pat(ast:pat()) -> ast:exc_type_pat().
exc_type_pat(P = {'atom', _, _}) -> P;
exc_type_pat(P = {var, _, _}) -> P;
exc_type_pat(P = {wildcard, _}) -> P;
exc_type_pat(P) -> errors:bug("Invalid class of a catch clause: ~w", P).

-spec stacktrace_pat(ast:pat()) -> ast:stacktrace_pat().
stacktrace_pat(P = {var, _, _}) -> P;
stacktrace_pat(P = {wildcard, _}) -> P;
stacktrace_pat(P) -> errors:bug("Invalid stacktrace of a catch clause: ~w", P).

% Translates function clauses into argument variables and a body (see ast:fun_decl()).
-spec trans_fun_clauses(ctx(), varenv_local:t(), [ast_erl:fun_clause(), ...])
                       -> {[ast:local_varname()], ast:exps()}.
trans_fun_clauses(Ctx, Env, Cs = [C = {clause, Anno, Ps, _, _} | _]) ->
    case is_var_only_clause(Cs) of
        true ->
            % one clause without a guard, its patterns are distinct variables
            {_, Qs, [], Body} = ?assert_pattern({_, _, [], _}, trans_fun_clause(Ctx, Env, C)),
            {[V || {var, _, {local_bind, V}} <- Qs], Body};
        false ->
            {Args, ArgEnv} =
                lists:mapfoldl(fun(_, E) -> varenv_local:insert_fresh(E) end, Env, Ps),
            % located at the first clause, apart from the fun itself
            G = ast:generated(fun_clauses, to_loc(Ctx, Anno)),
            Scrut = {tuple, G, [{var, G, {local_ref, A}} || A <- Args]},
            Clauses =
                lists:map(
                  fun(C) ->
                          {L, Qs, Guards, Body} = trans_fun_clause(Ctx, ArgEnv, C),
                          {case_clause, L, {tuple, ast:generated(fun_clauses, L), Qs}, Guards, Body}
                  end,
                  Cs),
            {Args, [{'case', G, Scrut, Clauses}]}
    end.

-spec is_var_only_clause([ast_erl:fun_clause()]) -> boolean().
is_var_only_clause([{clause, _, Ps, [], _}]) ->
    Names = [N || {var, _, N} <- Ps, N =/= '_'],
    length(Names) =:= length(Ps) andalso length(lists:usort(Names)) =:= length(Names);
is_var_only_clause(_) -> false.

-spec trans_fun_clause(ctx(), varenv_local:t(), ast_erl:fun_clause())
                      -> {ast:loc(), [ast:pat()], [ast:guard()], ast:exps()}.
trans_fun_clause(Ctx, Env, {clause, Anno, Ps, Guards, Body}) ->
    % shadow variables from outer context,
    % but don't bind multiple variables inside this pattern
    % mode shadow and using Env does not work for X = ..., fun(X, X) -> ...
    % as it would create X1= ..., fun(X2, X3) -> ...
    % whereas it should be X1= ..., fun(X2, X2) -> ...
    % -> use a new local context with bind_fresh,
    % but remember numbering of Variables in Env
    % merge afterwards, where QEnv0 takes precedence
    % map keys and sizes still refer to Env
    {Qs, QEnv0} = trans_pats(Ctx, Env, varenv_local:empty(Env), Ps, bind_fresh),
    QEnv = varenv_local:merge(Env, QEnv0),
    NewGuards = trans_guards(Ctx, QEnv, Guards),
    NewBody = trans_exp_seq_noenv(Ctx, QEnv, Body),
    {to_loc(Ctx, Anno), Qs, NewGuards, NewBody}.

% The outer variables referenced by the guards of an if, in order of first occurrence.
-spec if_guard_vars(ctx(), varenv_local:t(), [ast_erl:if_clause()]) -> [ast:local_varname()].
if_guard_vars(Ctx, Env, Cs) ->
    Guards = [trans_guards(Ctx, Env, Gs) || {clause, _, [], Gs, _} <- Cs],
    lists:uniq(utils:everything(fun({local_ref, V = {N, U}}) when is_atom(N), is_integer(U) -> {ok, V};
                                   (_) -> error
                                end, Guards)).

% `if G1 -> B1; ... end` becomes `case {X1, ..., Xn} of {Y1, ..., Yn} when G1[Y/X] -> B1[Y/X]; ...`
% for the outer variables Xi of the guards, so that the guards narrow the scrutinee.
-spec trans_if_clauses(ctx(), varenv_local:t(), [ast:local_varname()], [ast_erl:if_clause(), ...])
                      -> {[ast:case_clause(), ...], varenv_local:t()}.
trans_if_clauses(Ctx, Env, Vars, Cs) ->
    {NewClauses, NewEnvs} =
        lists:unzip(lists:map(fun(C) -> trans_if_clause(Ctx, Env, Vars, C) end, Cs)),
    {NewClauses, varenv_local:merge_envs(NewEnvs)}.

% The Yi shadow the Xi in the clause; afterwards the names refer to the Xi again.
-spec trans_if_clause(ctx(), varenv_local:t(), [ast:local_varname()], ast_erl:if_clause())
                     -> {ast:case_clause(), varenv_local:t()}.
trans_if_clause(Ctx, Env, Vars, {clause, Anno, [], Guards, Body}) ->
    Loc = to_loc(Ctx, Anno),
    G = ast:generated('if', Loc),
    {Ys, ClauseEnv} = lists:mapfoldl(fun({N, _}, E) -> varenv_local:insert(N, E) end, Env, Vars),
    Pat = case Ys of
              [] -> {wildcard, G};
              _ -> {tuple, G, [{var, G, {local_bind, Y}} || Y <- Ys]}
          end,
    NewGuards = trans_guards(Ctx, ClauseEnv, Guards),
    {NewBody, BodyEnv} = trans_exp_seq(Ctx, ClauseEnv, Body),
    NewEnv = lists:foldl(fun varenv_local:insert_var/2, BodyEnv, Vars),
    {{case_clause, Loc, Pat, NewGuards, NewBody}, NewEnv}.

-spec trans_qualifiers(ctx(), varenv_local:t(), [ast_erl:qualifier(), ...])
    -> {[ast:qualifier(), ...], varenv_local:t()}.
trans_qualifiers(Ctx, Env, Qs) ->
    thread_through_env(Env, Qs, fun(Env, Q) -> trans_qualifier(Ctx, Env, Q) end).

-spec trans_qualifier(ctx(), varenv_local:t(), ast_erl:qualifier())
    -> {ast:qualifier(), varenv_local:t()}.
trans_qualifier(Ctx, Env, Q = {generate, _, _, _}) -> trans_generator(Ctx, Env, Q);
trans_qualifier(Ctx, Env, Q = {generate_strict, _, _, _}) -> trans_generator(Ctx, Env, Q);
trans_qualifier(Ctx, Env, Q = {b_generate, _, _, _}) -> trans_generator(Ctx, Env, Q);
trans_qualifier(Ctx, Env, Q = {b_generate_strict, _, _, _}) -> trans_generator(Ctx, Env, Q);
trans_qualifier(Ctx, Env, Q = {m_generate, _, _, _}) -> trans_generator(Ctx, Env, Q);
trans_qualifier(Ctx, Env, Q = {m_generate_strict, _, _, _}) -> trans_generator(Ctx, Env, Q);
trans_qualifier(Ctx, Env, Q = {zip, _, _}) -> trans_generator(Ctx, Env, Q);
trans_qualifier(Ctx, Env, Exp) -> trans_exp(Ctx, Env, Exp). % filter

% A zip generator takes generators only, no filters.
-spec trans_generator(ctx(), varenv_local:t(), ast_erl:generators())
    -> {ast:generators(), varenv_local:t()}.
trans_generator(Ctx, Env, G) ->
    case G of
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
            {NewV, NewEnv2} = trans_pat(Ctx, Env, NewEnv1, ValPat, shadow),
            {{K, to_loc(Ctx, Anno), NewK, NewV, NewExp}, NewEnv2};
        % zip generator
        {zip, Anno, Gs} ->
            {NewGs, NewEnv} = thread_through_env(Env, Gs, fun(E, G1) -> trans_generator(Ctx, E, G1) end),
            {{zip, to_loc(Ctx, Anno), NewGs}, NewEnv}
    end.

-spec trans_map_assocs
    (ctx(), varenv_local:t(), [ast_erl:map_assoc_opt()]) -> {[ast:map_assoc_opt()], varenv_local:t()};
    (ctx(), varenv_local:t(), [ast_erl:map_assoc()]) -> {[ast:map_assoc()], varenv_local:t()}.
trans_map_assocs(Ctx, Env, As) ->
    thread_through_env(Env, As, fun(Env, A) -> trans_map_assoc(Ctx, Env, A) end).

-spec trans_map_assoc
    (ctx(), varenv_local:t(), ast_erl:map_assoc_opt()) -> {ast:map_assoc_opt(), varenv_local:t()};
    (ctx(), varenv_local:t(), ast_erl:map_assoc_req()) -> {ast:map_assoc_req(), varenv_local:t()}.
trans_map_assoc(Ctx, Env, {map_field_assoc, Anno, ExpKey, ExpVal}) ->
    {NewExpKey, Env1} = trans_exp(Ctx, Env, ExpKey),
    {NewExpVal, Env2} = trans_exp(Ctx, Env1, ExpVal),
    {{map_field_opt, to_loc(Ctx, Anno), NewExpKey, NewExpVal}, Env2};
trans_map_assoc(Ctx, Env, {map_field_exact, Anno, ExpKey, ExpVal}) ->
    {NewExpKey, Env1} = trans_exp(Ctx, Env, ExpKey),
    {NewExpVal, Env2} = trans_exp(Ctx, Env1, ExpVal),
    {{map_field_req, to_loc(Ctx, Anno), NewExpKey, NewExpVal}, Env2}.

% Expands record_field_other (the _ = Expr syntax) into individual record_field entries
% for each field not explicitly given. The record_field_other entry is removed.
-spec expand_record_field_other(ety_records:record_ty(),
    [{record_field, ast:loc(), atom(), ast:exp()}
     | {record_field_other, ast:loc(), ast:exp()}]) ->
    [{record_field, ast:loc(), atom(), ast:exp()}].
expand_record_field_other({_, DefFields}, Fields) ->
    % Split into explicit fields and the optional wildcard, a record expression has at most one
    Explicit = [F || F = {record_field, _, _, _} <- Fields],
    case [O || O = {record_field_other, _, _} <- Fields] of
        [] -> Explicit;
        [{record_field_other, Loc, Exp} | _] ->
            GivenNames = sets:from_list(
                [N || {record_field, _, N, _} <- Explicit],
                [{version, 2}]),
            WildcardFields =
                lists:filtermap(
                    fun({FieldName, _}) ->
                        case sets:is_element(FieldName, GivenNames) of
                            true -> false;
                            false -> {true, {record_field, ast:generated(record_field, Loc), FieldName, Exp}}
                        end
                    end,
                    DefFields),
            Explicit ++ WildcardFields
    end.

% Extracts default expressions from record field declarations.
% Returns a map from field name to the default expression.
-spec extract_field_defaults([ast_erl:record_field()]) -> #{ atom() => ast_erl:exp() }.
extract_field_defaults(Fields) ->
    Untyped = [case F of {typed_record_field, U, _} -> U; _ -> F end || F <- Fields],
    maps:from_list(
        [{Name, DefaultExp} || {record_field, _, {'atom', _, Name}, DefaultExp} <- Untyped]).

% Fills in record fields that are omitted during record creation. As in Erlang, an
% omitted field gets its default expression, or 'undefined' if it has no default.
% The default is evaluated in the scope of the record creation. It is annotated with the
% declared type of the field, so a default of another type is reported in the declaration.
-spec fill_record_defaults(ctx(), varenv_local:t(), ety_records:record_ty(), ast:loc(),
    [{record_field, ast:loc(), atom(), ast:exp()}]) ->
    [{record_field, ast:loc(), atom(), ast:exp()}].
fill_record_defaults(Ctx, Env, {RecName, DefFields}, Loc, GivenFields) ->
    {DefFile, Defaults} =
        maps:get(RecName, Ctx#ctx.record_defaults, {Ctx#ctx.current_file, #{}}),
    DefCtx = Ctx#ctx{ current_file = DefFile },
    GivenNames = sets:from_list(
        [N || {record_field, _, N, _} <- GivenFields],
        [{version, 2}]),
    G = ast:generated(record_field, Loc),
    DefaultFields =
        [{record_field, G, N,
          case Defaults of
              #{N := DefaultExp} ->
                  E = trans_exp_noenv(DefCtx, Env, DefaultExp),
                  case Ty of
                      {predef, any} -> E;
                      _ -> {annotate, ast:generated(record_field, ast:loc_exp(E)), E, Ty}
                  end;
              _ -> {'atom', G, undefined}
          end}
         || {N, Ty} <- DefFields, not sets:is_element(N, GivenNames)],
    GivenFields ++ DefaultFields.

% {Name, X1, ..., Xn} for a record. Fields has an entry for every field of the record,
% the first entry of a field counts.
-spec record_tuple(ast:loc(), ety_records:record_ty(), [{record_field, ast:loc(), atom(), T}]) ->
          {tuple, ast:loc(), [{'atom', ast:loc(), atom()} | T]}.
record_tuple(Loc, {Name, DefFields}, Fields) ->
    Xs = lists:map(fun({N, _}) -> record_field_value(N, Fields) end, DefFields),
    {tuple, Loc, [{'atom', Loc, Name} | Xs]}.

-spec record_field_value(atom(), [{record_field, ast:loc(), atom(), T}]) -> T.
record_field_value(N, [{record_field, _, N, X} | _]) -> X;
record_field_value(N, [_ | Fields]) -> record_field_value(N, Fields);
record_field_value(N, []) -> errors:bug("no value for record field ~w", [N]).

% E#RecName.FieldName is '#RecName.FieldName'(E), a function of the symtab
% (see ety_records:readers/1).
-spec record_read(ctx(), ast:loc(), atom(), atom(), ast:exp()) -> ast:exp().
record_read(Ctx, Loc, RecName, FieldName, E) ->
    _ = record_field_pos(Loc, lookup_record(Ctx, Loc, RecName), FieldName),
    G = ast:generated(record_field, Loc),
    {call, G, {var, G, {ref, ety_records:reader_name(RecName, FieldName), 1}}, [E]}.

% E#r{b = X} is {r, '#r.a'(E), X, '#r.c'(E)}. E is bound to a variable first, unless
% it is one.
-spec trans_record_update(ctx(), varenv_local:t(), ast:loc(), ast:exp(), atom(),
                          [{record_field, ast:loc(), atom(), ast:exp()}]) -> ast:exp().
trans_record_update(Ctx, _Env, Loc, E = {var, _, {local_ref, _}}, Name, Fields) ->
    RecTy = {_, DefFields} = lookup_record(Ctx, Loc, Name),
    G = ast:generated(record_field, Loc),
    Given = [N || {record_field, _, N, _} <- Fields],
    Kept = [{record_field, G, N, record_read(Ctx, Loc, Name, N, E)}
            || {N, _} <- DefFields, not lists:member(N, Given)],
    Tuple = record_tuple(Loc, RecTy, Fields ++ Kept),
    case {Kept, Given} of
        % all fields are replaced, E still has to be the record
        {[], [N | _]} -> {block, G, [record_read(Ctx, Loc, Name, N, E), Tuple]};
        _ -> Tuple
    end;
trans_record_update(Ctx, Env, Loc, E, Name, Fields) ->
    G = ast:generated(record_field, Loc),
    {V, VEnv} = varenv_local:insert_fresh(Env),
    Ref = {var, ast:loc_exp(E), {local_ref, V}},
    Body = trans_record_update(Ctx, VEnv, Loc, Ref, Name, Fields),
    {'case', G, E, [{case_clause, G, {var, G, {local_bind, V}}, [], [Body]}]}.

-spec lookup_record(ctx(), ast:loc(), atom()) -> ety_records:record_ty().
lookup_record(Ctx, Loc, Name) ->
    case maps:find(Name, Ctx#ctx.records) of
        {ok, RecTy} -> RecTy;
        error -> errors:name_error(Loc, "record ~w not defined", [Name])
    end.

% Position of a field in the tuple representing the record. Position 1 holds the
% record name, so the first field is at position 2.
-spec record_field_pos(ast:loc(), ety_records:record_ty(), atom()) -> pos_integer().
record_field_pos(Loc, {RecName, DefFields}, FieldName) ->
    case utils:assocs_find_index(FieldName, DefFields) of
        {ok, _, I} -> ?assert_type(I + 2, pos_integer());
        error -> errors:name_error(Loc, "field ~w not defined in record ~w", [FieldName, RecName])
    end.

% #Name.Field is the constant position of Field in the record tuple.
-spec trans_record_index(ctx(), ast:loc(), atom(), atom()) -> {integer, ast:loc(), pos_integer()}.
trans_record_index(Ctx, Loc, RecName, FieldName) ->
    {integer, Loc, record_field_pos(Loc, lookup_record(Ctx, Loc, RecName), FieldName)}.

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
             trans_exp_noenv(Ctx, varenv_local:empty(), DefaultExp)}
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
    {ok, Tokens, _EndLocation} = ?assert_pattern({ok, _, _}, erl_scan:string(AttrSrc)),
    % the variables in the outer function -type definition are not in scope in the annotation
    % at some point, we could extend this like Haskell's ScopeTypeVariables, if there is any need
    case erl_parse:parse_form(Tokens) of
        {ok, {attribute, _, type, Def = {t, _Type, []}}} ->
            {_, {ty_scheme, [], TyNew}} =
                ?assert_pattern({_, {ty_scheme, [], _}}, trans_tydef(Ctx, Def)),
            {ok, TyNew};
        _ -> error
    end.

% Stores a record override variant in the ETS table for later retrieval.
% Used when a self-referencing record has field overrides (e.g., #rr{name :: any()}).
% Returns the generated variant type name.
-spec store_record_variant(ctx(), atom(), [ety_records:record_field()]) -> atom().
store_record_variant(Ctx, RecName, Overrides) ->
    Tab = Ctx#ctx.record_variants,
    N = length(ets:lookup(Tab, RecName)) + 1,
    VariantName = list_to_atom("$record$" ++ atom_to_list(RecName) ++ "$v" ++ integer_to_list(N)),
    ets:insert(Tab, {RecName, VariantName, Overrides}),
    VariantName.

% Collects and removes all record override variants for a record from the ETS table.
-spec collect_record_variants(ctx(), atom()) -> [{atom(), [ety_records:record_field()]}].
collect_record_variants(Ctx, RecName) ->
    Tab = Ctx#ctx.record_variants,
    Results = [{VName, Ov} || {_, VName, Ov} <- ets:lookup(Tab, RecName)],
    ets:delete(Tab, RecName),
    % as store_record_variant/3 has put them into the table
    ?assert_type(Results, [{atom(), [ety_records:record_field()]}]).

-ifdef(TEST).

test_ctx() ->
    #ctx{ path = ".", current_file = ".", module_name = ast_transform, funenv = varenv:empty("function"), records = #{},
          record_variants = ets:new(test_record_variants, [bag]) }.

parse_type_test() ->
    Ctx = test_ctx(),
    {ok, {predef_alias, string}} = parse_type(Ctx, "string()"),
    {ok, {singleton, a}} = parse_type(Ctx, "a"),

    % user types are supported (no locations, though)
    {ok, {named, _, _, [{named, _, _, _}]}} = parse_type(Ctx, "parser(command())"),

    % builtin types of etylizer
    {ok, {cons, {singleton, a}, {cons, {predef, integer}, {empty_list}}}} =
        parse_type(Ctx, "etylizer:cons(a, etylizer:cons(integer(), []))"),
    ?assertThrow({etylizer, ty_error, _}, parse_type(Ctx, "etylizer:cons(a)")),

    % type error
    error = parse_type(Ctx, "not a type"),

    % free type variables not supported
    ?assertThrow({etylizer, name_error, _}, parse_type(Ctx, "A")),

    % type variables are only bound in the -spec annotation
    % therefore, no type variables are supported in annotations
    ?assertThrow({etylizer, name_error, _}, parse_type(Ctx, "fun((A) -> A)")),

    ok.

-endif.
