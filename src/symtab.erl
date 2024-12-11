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
    std_symtab/1,
    extend_symtab/3,
    extend_symtab_with_fun_env/2,
    empty/0,
    extend_symtab_with_module_list/3,
    dump_symtab/2
]).

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
              modules :: mod_env()
}).

-opaque t() :: #tab{}.

-spec dump_symtab(string(), t()) -> ok.
dump_symtab(Msg, Tab) ->
    ?LOG_DEBUG("~s~nFunctions:~n~s~ntypes:~n~s~nOperators:~n~s~nRecords:~n~s",
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
empty() -> #tab { funs = #{}, ops = #{}, types = #{}, records = #{}, modules = #{} }.

-spec std_symtab(paths:search_path()) -> t().
std_symtab(SearchPath) ->
    ?LOG_NOTE("Building symtab for standard library ..."),
    Funs =
        lists:foldl(fun({Name, Arity, T}, Map) -> maps:put({qref, erlang, Name, Arity}, T, Map) end,
                    #{},
                    stdtypes:builtin_funs()),
    Ops =
        lists:foldl(fun({Name, Arity, T}, Map) -> maps:put({Name, Arity}, T, Map) end,
                    #{},
                    stdtypes:builtin_ops()),
    Tab = #tab { funs = Funs, ops = Ops, types = #{}, records = #{}, modules = #{} },
    ExtTab = extend_symtab_with_module_list(Tab, SearchPath, [erlang]),
    ?LOG_NOTE("Done building symtab for standard library"),
    ExtTab.

-type ref() :: ref | {qref, ModuleName::atom()}.

-spec extend_symtab(file:filename(), [ast:form()], t()) -> t().
extend_symtab(Filename, Forms, Tab) ->
    extend_symtab_internal(Filename, Forms, ref, Tab).

-spec extend_symtab(file:filename(), [ast:form()], atom(), t()) -> t().
extend_symtab(Filename, Forms, Module, Tab) ->
    extend_symtab_internal(Filename, Forms, {qref, Module}, Tab).

-spec extend_symtab_internal(file:filename(), [ast:form()], ref(), t()) -> t().
extend_symtab_internal(Filename, Forms, RefType, Tab) ->
    case utils:file_exists(Filename) of
        true -> ok;
        false ->
            errors:some_error("File ~s does not exist", [Filename])
    end,
    ModuleName = ast_utils:modname_from_path(Filename),
    IsNew =
        case maps:get(ModuleName, Tab#tab.modules, error) of
            error -> true;
            ModulePath ->
                case utils:is_same_file(Filename, ModulePath) of
                    true -> false;
                    false ->
                        errors:some_error("Projects contains two different files defining the same module ~w: ~s and ~s",
                            [ModuleName, ModulePath, Filename])
                end
        end,
    case IsNew of
        false -> Tab;
        true ->
            NewTab =
                lists:foldl(
                    fun(Form, Tab) ->
                        case Form of
                            {attribute, _, spec, Name, Arity, T, _} ->
                                Tab#tab { funs = maps:put(create_ref_tuple(RefType, Name, Arity), T, Tab#tab.funs) };
                            {attribute, _, type, _, {Name, TyScm = {ty_scheme, TyVars, _}}} ->
                                Arity = length(TyVars),
                                Tab#tab { types = maps:put({ty_key, ModuleName, Name, Arity}, TyScm, Tab#tab.types) };
                            {attribute, _, record, {RecordName, Fields}} ->
                                RecordTy = records:record_ty_from_decl(RecordName, Fields),
                                Tab#tab { records = maps:put(RecordName, RecordTy, Tab#tab.records) };
                            _ ->
                                Tab
                        end
                    end,
                    Tab#tab { modules = maps:put(ModuleName, Filename, Tab#tab.modules) },
                    Forms),
            NewTab
    end.

-spec extend_symtab_with_fun_env(fun_env(), t()) -> t().
extend_symtab_with_fun_env(Env, Tab) -> Tab#tab { funs = maps:merge(Tab#tab.funs, Env) }.

-spec create_ref_tuple(ref(), string(), arity()) -> tuple().
create_ref_tuple(ref, Name, Arity) ->
    {ref, Name, Arity};
create_ref_tuple({qref, Module}, Name, Arity) ->
    {qref, Module, Name, Arity}.

% Extends the symtab with all definitions from the given modules. If such definitions refer
% to other modules via their type specs, such modules are added as well. (We could add only
% the types from these modules, but for simplicity, we add everything.)
-spec extend_symtab_with_module_list(symtab:t(), paths:search_path(), [atom()]) -> symtab:t().
extend_symtab_with_module_list(Symtab, SearchPath, Modules) ->
    traverse_module_list(SearchPath, Symtab, Modules).

-spec traverse_module_list(paths:search_path(), t(), [ast:mod_name()]) -> t().
traverse_module_list(SearchPath, Symtab, [CurrentModule | RemainingModules]) ->
    case maps:get(CurrentModule, Symtab#tab.modules, error) of
        error ->
            % It's a new module
            Entry = {_, Filename, _} = paths:find_module_path(SearchPath, CurrentModule),
            Forms = retrieve_forms_for_source(Entry),
            NewSymtab = extend_symtab(Filename, Forms, CurrentModule, Symtab),
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
            ?LOG_DEBUG("Additional modukes for ~w: ~200p", CurrentModule, AdditionalModules),
            traverse_module_list(SearchPath, NewSymtab, RemainingModules ++ AdditionalModules);
        _ -> traverse_module_list(SearchPath, Symtab, RemainingModules)
    end;
traverse_module_list(_, Symtab, []) ->
    Symtab.

-spec retrieve_forms_for_source(paths:search_path_entry()) -> ast:forms().
retrieve_forms_for_source({Kind, Src, Includes}) ->
    case Kind of
        local -> parse_cache:parse(intern, Src);
        _ -> parse_cache:parse({extern, Includes}, Src)
    end.
