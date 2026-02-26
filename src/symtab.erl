-module(symtab).

% @doc A symbol table for information either defined in the current or some external module.

-include("log.hrl").

-compile([nowarn_shadow_vars]).

-export_type([
    t/0,
    fun_env/0,
    ty_env/0,
    record_env/0,
    op_env/0
]).

-export([
    lookup_fun/3,
    find_fun/2,
    lookup_op/4,
    lookup_ty/3,
    lookup_record/3,
    std_symtab/2,
    extend_symtab/4,
    extend_symtab_with_fun_env/2,
    empty/0,
    extend_symtab_with_module_list/4,
    dump_symtab/2, overlay_symtab/1,
    get_types/1,
    is_nominal/2
]).


-ifdef(TEST). % for tally tests
-export([
    from_types/1
]).
-endif.

-include("etylizer.hrl").

-type fun_env() :: #{ ast:global_ref() => ast:ty_scheme() }.
-type ty_key() :: {ty_key, Module::atom(), Name::atom(), Arity::arity()}.
-type ty_env() :: #{ ty_key() => ast:ty_scheme() }.
-type record_env() :: #{ atom() => records:record_ty() }.
-type op_env() :: #{ {atom(), arity()} => ast:ty_scheme() }.
-type mod_env() :: #{ ast:mod_name() => file:filename() }.
-record(tab, {
              funs :: fun_env(),
              ops :: op_env(),
              types :: ty_env(),
              records :: record_env(),
              modules :: mod_env(),
              nominals :: sets:set(ty_key())
}).

-type t() :: #tab{}.

-spec get_types(t()) -> ty_env().
get_types(#tab{types = Types}) -> Types.

-spec is_nominal(ast:ty_ref(), t()) -> boolean().
is_nominal(Ref, Tab) ->
    Key = case Ref of
              {ty_ref, M, N, A} -> {ty_key, M, N, A};
              {ty_qref, M, N, A} -> {ty_key, M, N, A}
          end,
    sets:is_element(Key, Tab#tab.nominals).

-spec dump_symtab(string(), t()) -> ok.
dump_symtab(Msg, Tab) ->
    ?LOG_DEBUG("~s~nFunctions: ~w~nTypes: ~w~nOperators: ~w~nRecords: ~w",
        Msg,
        maps:keys(Tab#tab.funs),
        maps:keys(Tab#tab.types),
        maps:keys(Tab#tab.ops),
        maps:keys(Tab#tab.records)),
    ?LOG_TRACE("~s~nFunctions:~n~s~ntypes:~n~s~nOperators:~n~s~nRecords:~n~s",
        Msg,
        pretty:render_fun_env(Tab#tab.funs),
        pretty:render_ty_env(Tab#tab.types),
        pretty:render_op_env(Tab#tab.ops),
        pretty:render_record_env(Tab#tab.records)).

-spec dump_symtab_not_defined(string(), string(), t()) -> ok.
dump_symtab_not_defined(Key, What, Tab) ->
    Msg = utils:sformat("Key ~s not defined as ~s in symtab", Key, What),
    dump_symtab(Msg, Tab).

% Get the type declared for a function. The location is the use-site
% If no such name exists, an error is thrown.
-spec lookup_fun(ast:global_ref(), ast:loc(), t()) -> ast:ty_scheme().
lookup_fun(Ref, Loc, Tab) ->
    case find_fun(Ref, Tab) of
        {ok, X} -> X;
        error ->
            RefStr = pretty:render(pretty:ref(Ref)),
            dump_symtab_not_defined(RefStr, "function", Tab),
            errors:name_error(Loc, "function ~s undefined", RefStr)
    end.

-spec find_fun(ast:global_ref(), t()) -> t:opt(ast:ty_scheme()).
find_fun(Ref, Tab) -> maps:find(Ref, Tab#tab.funs).

% Get the type for an operator
-spec lookup_op(atom(), arity(), ast:loc(), t()) -> ast:ty_scheme().
lookup_op(Name, Arity, Loc, Tab) ->
    case find_op(Name, Arity, Tab) of
        {ok, X} -> X;
        error ->
            S = pretty:render(pretty:arity(Name, Arity)),
            dump_symtab_not_defined(S, "operator", Tab),
            errors:name_error(Loc, "operator ~s undefined", S)
    end.

-spec find_op(atom(), arity(), t()) -> t:opt(ast:ty_scheme()).
find_op(Name, Arity, Tab) -> maps:find({Name, Arity}, Tab#tab.ops).

% Get the type declared for a type. The location is the use-site
% If no such name exists, an error is thrown.
-spec lookup_ty(ast:ty_ref(), ast:loc(), t()) -> ast:ty_scheme().
lookup_ty(Ref, Loc, Tab) ->
    case find_ty(Ref, Tab) of
        {ok, X} -> X;
        error ->
            RefStr = pretty:render(pretty:ref(Ref)),
            dump_symtab_not_defined(RefStr, "type", Tab),
            errors:name_error(Loc, "type ~s undefined", RefStr)
    end.

-spec find_ty(ast:ty_ref(), t()) -> t:opt(ast:ty_scheme()).
find_ty(Ref, Tab) ->
    TyRef = case Ref of
                {ty_ref, M, N, A} -> {ty_key, M, N, A};
                {ty_qref, M, N ,A} -> {ty_key, M, N, A}
            end ,
    maps:find(TyRef, Tab#tab.types).

-spec lookup_record(atom(), ast:loc(), t()) -> records:record_ty().
lookup_record(Name, Loc, Tab) ->
    case find_record(Name, Tab) of
        {ok, X} -> X;
        error ->
            dump_symtab_not_defined(utils:sformat("~w", Name), "record", Tab),
            errors:name_error(Loc, "record ~w undefined", Name)
    end.

-spec find_record(atom(), t()) -> t:opt(records:record_ty()).
find_record(Name, Tab) -> maps:find(Name, Tab#tab.records).

-spec symbols_for_module(atom(), t()) -> [{ref, atom(), arity()}].
symbols_for_module(Mod, Tab) ->
    lists:filtermap(
        fun({K,_}) ->
            case K of
                {qref, M, N, A} when M =:= Mod -> {true, {ref, N, A}};
                {ty_key, M, N, A} when M =:= Mod -> {true, {ref, N, A}};
                _ -> false
            end
        end,
        maps:to_list(Tab#tab.funs) ++ maps:to_list(Tab#tab.types)
        ).

-spec empty() -> t().
empty() -> #tab { funs = #{}, ops = #{}, types = #{}, records = #{}, modules = #{}, nominals = sets:new([{version, 2}]) }.

-spec std_symtab(paths:search_path(), t()) -> t().
std_symtab(SearchPath, OverlaySymtab) ->
    CacheKey = erlang:phash2(OverlaySymtab),
    case persistent_term:get(std_symtab_cache, undefined) of
        {CacheKey, CachedTab} ->
            ?LOG_DEBUG("Using cached standard symtab"),
            ?assert_type(CachedTab, t());
        _ ->
            Tab = build_std_symtab(SearchPath, OverlaySymtab),
            persistent_term:put(std_symtab_cache, {CacheKey, Tab}),
            Tab
    end.

-spec build_std_symtab(paths:search_path(), t()) -> t().
build_std_symtab(SearchPath, OverlaySymtab) ->
    ?LOG_DEBUG("Building symtab for standard library ..."),
    Funs =
        lists:foldl(fun({Name, Arity, T}, Map) ->
            maps:put({qref, erlang, Name, Arity}, T, Map) end,
                    #{},
                    stdtypes:builtin_funs()),
    Ops =
        lists:foldl(fun({Name, Arity, T}, Map) -> maps:put({Name, Arity}, T, Map) end,
                    #{},
                    stdtypes:builtin_ops()),
    Tab = #tab { funs = Funs, ops = Ops, types = #{}, records = #{}, modules = #{}, nominals = sets:new([{version, 2}]) },
    ExtTab = extend_symtab_with_module_list(Tab, SearchPath, [erlang], OverlaySymtab),
    % Merge overlay types into the main symtab so they are available for type resolution
    ExtTab2 = ExtTab#tab { types = maps:merge(ExtTab#tab.types, OverlaySymtab#tab.types) },
    ?LOG_DEBUG("Done building symtab for standard library"),
    ExtTab2.

-spec overlay_symtab([ast:form()]) -> t().
overlay_symtab(OverlayForms) ->
    ?LOG_DEBUG("Building symtab for overlay file ..."),
    ModuleName = lists:foldl(fun(Form, Acc) ->
        case Form of
            {attribute, _, module, M} -> M;
            _ -> Acc
        end
    end, undefined, OverlayForms),
    lists:foldl(fun(Form, Tab) -> overlay_process_form(Form, Tab, ModuleName) end,
    empty(),
    OverlayForms).

-spec overlay_process_form(ast:form(), t(), atom() | undefined) -> t().
overlay_process_form(Form, Tab, ModuleName) ->
    case Form of
        {attribute, _, spec, Name, Arity, T, _} ->
            overlay_add_spec(Name, Arity, T, Tab);
        {attribute, _, type, Visibility, {Name, TyScm = {ty_scheme, TyVars, _}}} when ModuleName =/= undefined ->
            overlay_add_type(Visibility, Name, TyScm, TyVars, Tab, ModuleName);
        _ -> Tab
    end.

-spec overlay_add_spec(atom(), arity(), ast:ty_scheme(), t()) -> t().
overlay_add_spec(Name, Arity, T, Tab) ->
    ?LOG_DEBUG("Overlay added for ~w/~p", Name, Arity),
    [Module, FunName] = ?assert_pattern([_, _], string:split(atom_to_list(Name), ":")),
    Tab#tab { funs = maps:put(create_ref_tuple({qref, list_to_atom(Module)}, list_to_atom(FunName), Arity), T, Tab#tab.funs) }.

-spec overlay_add_type(transparent | opaque | nominal, atom(), ast:ty_scheme(), [ast:bounded_tyvar()], t(), atom()) -> t().
overlay_add_type(Visibility, Name, TyScm, TyVars, Tab, ModuleName) ->
    Arity = length(TyVars),
    Key = {ty_key, ModuleName, Name, Arity},
    ?LOG_DEBUG("Overlay type added: ~w/~p", Name, Arity),
    Tab1 = Tab#tab { types = maps:put(Key, TyScm, Tab#tab.types) },
    case Visibility of
        nominal -> Tab1#tab { nominals = sets:add_element(Key, Tab1#tab.nominals) };
        _ -> Tab1
    end.

-type ref() :: ref | {qref, ModuleName::atom()}.

-spec extend_symtab(file:filename(), [ast:form()], t(), t()) -> t().
extend_symtab(Filename, Forms, Tab, OverlaySymtab) ->
    extend_symtab_internal(Filename, Forms, ref, Tab, OverlaySymtab).

-spec extend_symtab(file:filename(), [ast:form()], atom(), t(), t()) -> t().
extend_symtab(Filename, Forms, Module, Tab, OverlaySymtab) ->
    extend_symtab_internal(Filename, Forms, {qref, Module}, Tab, OverlaySymtab).

-spec is_exported(ast:forms(), atom(), arity()) -> boolean().
is_exported(Forms, Name, Arity) ->
    lists:any(fun(Form) ->
            case Form of
                {attribute, _, export, Exports} ->
                    lists:member({Name, Arity}, Exports);
                {attribute, _, compile, export_all} -> true;
                {attribute, _, compile, Opts} when is_list(Opts) ->
                    lists:member(export_all, Opts);
                _ -> false
            end
        end, Forms).


-spec extend_symtab_internal(file:filename(), [ast:form()], ref(), t(), t()) -> t().
extend_symtab_internal(Filename, Forms, RefType, Tab, OverlaySymtab) ->
    case utils:file_exists(Filename) of
        true -> ok;
        false ->
            errors:some_error("File ~s does not exist", [Filename])
    end,
    ModuleName = ast_utils:modname_from_path(Filename),
    lists:foldl(
        fun(Form, AccTab) -> extend_process_form(Form, AccTab, RefType, ModuleName, Forms, OverlaySymtab) end,
Tab#tab { modules = maps:put(ModuleName, Filename, Tab#tab.modules) },
Forms).

-spec extend_process_form(ast:form(), t(), ref(), atom(), [ast:form()], t()) -> t().
extend_process_form(Form, Tab, RefType, ModuleName, Forms, OverlaySymtab) ->
    case Form of
        {attribute, _, spec, Name, Arity, T, _} ->
            extend_add_spec(Name, Arity, T, Tab, RefType, ModuleName, Forms, OverlaySymtab);
        {attribute, _, type, Visibility, {Name, TyScm = {ty_scheme, TyVars, _}}} ->
            extend_add_type(Visibility, Name, TyScm, TyVars, Tab, ModuleName);
        {attribute, _, record, {RecordName, Fields}} ->
            extend_add_record(RecordName, Fields, Tab, ModuleName);
        _ -> Tab
    end.

-spec extend_add_spec(atom(), arity(), ast:ty_scheme(), t(), ref(), atom(), [ast:form()], t()) -> t().
extend_add_spec(Name, Arity, T, Tab, RefType, ModuleName, Forms, OverlaySymtab) ->
    Ref = create_ref_tuple(RefType, Name, Arity),
    case find_fun(Ref, OverlaySymtab) of
        error ->
            ?LOG_TRACE("No Overlay found for ~w:~w/~p", ModuleName, Name, Arity),
            maybe_add_qref(RefType, ModuleName, Name, Arity, T, Forms, Tab);
        {ok, OverlayT} ->
            ?LOG_DEBUG("Overlay found for ~w:~w/~p", ModuleName, Name, Arity),
            Tab#tab { funs = maps:put(create_ref_tuple(RefType, Name, Arity), OverlayT, Tab#tab.funs) }
    end.

-spec extend_add_type(transparent | opaque | nominal, atom(), ast:ty_scheme(), [ast:bounded_tyvar()], t(), atom()) -> t().
extend_add_type(Visibility, Name, TyScm, TyVars, Tab, ModuleName) ->
    Arity = length(TyVars),
    Key = {ty_key, ModuleName, Name, Arity},
    Tab1 = Tab#tab { types = maps:put(Key, TyScm, Tab#tab.types) },
    case Visibility of
        nominal -> Tab1#tab { nominals = sets:add_element(Key, Tab1#tab.nominals) };
        _ -> Tab1
    end.

-spec extend_add_record(atom(), [ast:record_field()], t(), atom()) -> t().
extend_add_record(RecordName, Fields, Tab, ModuleName) ->
    RecordTy = records:record_ty_from_decl(RecordName, Fields),
    RecTypeName = records:record_type_name(RecordName),
    RecTupleType = records:encode_record_ty(RecordTy),
    RecTyScheme = {ty_scheme, [], RecTupleType},
    Tab#tab {
        records = maps:put(RecordName, RecordTy, Tab#tab.records),
        types = maps:put({ty_key, ModuleName, RecTypeName, 0}, RecTyScheme, Tab#tab.types)
    }.

-spec extend_symtab_with_fun_env(fun_env(), t()) -> t().
extend_symtab_with_fun_env(Env, Tab) -> Tab#tab { funs = maps:merge(Tab#tab.funs, Env) }.


-spec maybe_add_qref(ref(), ast:mod_name(), atom(), arity(), ast:ty_scheme(), ast:forms(), t()) -> t().
maybe_add_qref({qref, _}, Module, Name, Arity, Type, _, Tab) ->
    Tab#tab { funs = maps:put(create_ref_tuple({qref, Module}, Name, Arity), Type, Tab#tab.funs) };
maybe_add_qref(ref, Module, Name, Arity, Type, Forms, Tab) ->
    NewTab = Tab#tab { funs = maps:put(create_ref_tuple(ref, Name, Arity), Type, Tab#tab.funs) },
    case is_exported(Forms, Name, Arity) of
        true -> NewTab#tab { funs = maps:put(create_ref_tuple({qref, Module}, Name, Arity), Type, NewTab#tab.funs) };
        false -> NewTab
    end.

-spec create_ref_tuple(ref(), atom(), arity()) -> ast:global_ref().
create_ref_tuple(ref, Name, Arity) ->
    {ref, Name, Arity};
create_ref_tuple({qref, Module}, Name, Arity) ->
    {qref, Module, Name, Arity}.

% Extends the symtab with all definitions from the given modules. If such definitions refer
% to other modules via their type specs, such modules are added as well. (We could add only
% the types from these modules, but for simplicity, we add everything.)
-spec extend_symtab_with_module_list(symtab:t(), paths:search_path(), [atom()], t()) -> symtab:t().
extend_symtab_with_module_list(Symtab, SearchPath, Modules, OverlaySymtab) ->
    traverse_module_list(SearchPath, Symtab, Modules, OverlaySymtab).

-spec traverse_module_list(paths:search_path(), t(), [ast:mod_name()], t()) -> t().
traverse_module_list(SearchPath, Symtab, [CurrentModule | RemainingModules], OverlaySymtab) ->
    case maps:get(CurrentModule, Symtab#tab.modules, error) of
        error ->
            % It's a new module
            Entry = {_, Filename, _} = paths:find_module_path(SearchPath, CurrentModule),
            Forms = retrieve_forms_for_source(Entry),
            NewSymtab = extend_symtab(Filename, Forms, CurrentModule, Symtab, OverlaySymtab),
            ?LOG_DEBUG("Extended symtab with entries from ~p", CurrentModule),
            case log:allow(trace) of
                true ->
                    NewSymbols = symbols_for_module(CurrentModule, NewSymtab),
                    ?LOG_TRACE("New symbols from module ~p: ~s", CurrentModule,
                        pretty:render_list(fun pretty:ref/1, NewSymbols));
                false ->
                    ok
            end,
            AdditionalModules = ast_utils:referenced_modules_via_types(Forms),
            ?LOG_DEBUG("Additional modules for ~w: ~200p", CurrentModule, AdditionalModules),
            traverse_module_list(SearchPath, NewSymtab, RemainingModules ++ AdditionalModules, OverlaySymtab);
        _ -> traverse_module_list(SearchPath, Symtab, RemainingModules, OverlaySymtab)
    end;
traverse_module_list(_, Symtab, [], _) ->
    Symtab.

-spec retrieve_forms_for_source(paths:search_path_entry()) -> ast:forms().
retrieve_forms_for_source({Kind, Src, Includes}) ->
    case Kind of
        local -> parse_cache:parse(intern, Src);
        _ -> parse_cache:parse({extern, Includes}, Src)
    end.

-ifdef(TEST).
-spec from_types(any()) -> t().
from_types(Types) when is_list(Types) -> (empty())#tab{types = maps:from_list(Types)};
from_types(Types) when is_map(Types) -> (empty())#tab{types = Types}.
-endif.
