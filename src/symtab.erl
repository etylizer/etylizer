-module(symtab).

% @doc A symbol table for information either defined in the current or some external module.

-include_lib("log.hrl").
-include_lib("parse.hrl").
-include_lib("ety_main.hrl").

-compile([nowarn_shadow_vars]).

-export_type([
    t/0
]).

-export([
    lookup_fun/3,
    find_fun/2,
    lookup_op/4,
    find_op/3,
    lookup_ty/3,
    find_ty/2,
    std_symtab/0,
    extend_symtab/2,
    extend_symtab/3,
    empty/0,
    extend_symtab_with_module_list/3
]).

-record(tab, {
              funs :: #{ ast:global_ref() => ast:ty_scheme() },
              ops :: #{ {atom(), arity()} => ast:ty_scheme() },
              types :: #{ ast:global_ref() => ast:ty_scheme() }
}).

-opaque t() :: #tab{}.

% Get the type declared for a function. The location is the use-site
% If no such name exists, an error is thrown.
-spec lookup_fun(ast:global_ref(), ast:loc(), t()) -> ast:ty_scheme().
lookup_fun(Ref, Loc, Tab) ->
    case find_fun(Ref, Tab) of
        {ok, X} -> X;
        error -> errors:name_error(Loc, "function ~s undefined", pp:global_ref(Ref))
    end.

-spec find_fun(ast:global_ref(), t()) -> t:opt(ast:ty_scheme()).
find_fun(Ref, Tab) -> maps:find(Ref, Tab#tab.funs).

% Get the type for an operator
-spec lookup_op(atom(), arity(), ast:loc(), t()) -> ast:ty_scheme().
lookup_op(Name, Arity, Loc, Tab) ->
    case find_op(Name, Arity, Tab) of
        {ok, X} -> X;
        error -> errors:name_error(Loc, "operator ~w undefined for ~w arguments", [Name, Arity])
    end.

-spec find_op(atom(), arity(), t()) -> t:opt(ast:ty_scheme()).
find_op(Name, Arity, Tab) -> maps:find({Name, Arity}, Tab#tab.ops).

% Get the type declared for a type. The location is the use-site
% If no such name exists, an error is thrown.
-spec lookup_ty(ast:global_ref(), ast:loc(), t()) -> ast:ty_scheme().
lookup_ty(Ref, Loc, Tab) ->
    case find_ty(Ref, Tab) of
        {ok, X} -> X;
        error -> errors:name_error(Loc, "type ~s undefined", pp:global_ref(Ref))
    end.

-spec find_ty(ast:global_ref(), t()) -> t:opt(ast:ty_scheme()).
find_ty(Ref, Tab) -> maps:find(Ref, Tab#tab.types).

-spec empty() -> t().
empty() -> #tab { funs = #{}, ops = #{}, types = #{} }.

-spec std_symtab() -> t().
std_symtab() ->
    Funs =
        lists:foldl(fun({Name, Arity, T}, Map) -> maps:put({qref, erlang, Name, Arity}, T, Map) end,
                    #{},
                    stdtypes:builtin_funs()),
    Ops =
        lists:foldl(fun({Name, Arity, T}, Map) -> maps:put({Name, Arity}, T, Map) end,
                    #{},
                    stdtypes:builtin_ops()),
    #tab { funs = Funs, ops = Ops, types = #{} }.

-spec extend_symtab([ast:form()], t()) -> t().
extend_symtab(Forms, Tab) ->
    extend_symtab_internal(Forms, {ref}, Tab).

-spec extend_symtab([ast:form()], atom(), t()) -> t().
extend_symtab(Forms, Module, Tab) ->
    extend_symtab_internal(Forms, {qref, Module}, Tab).

extend_symtab_internal(Forms, RefType, Tab) ->
    lists:foldl(
      fun(Form, Tab) ->
              case Form of
                  {attribute, _, spec, Name, Arity, T, _} ->
                      Tab#tab { funs = maps:put(create_ref_tuple(RefType, Name, Arity), T, Tab#tab.funs) };
                  {attribute, _, type, _, {Name, TyScm = {ty_scheme, TyVars, _}}} ->
                      Arity = length(TyVars),
                      Tab#tab { types = maps:put(create_ref_tuple(RefType, Name, Arity), TyScm, Tab#tab.types) };
                  _ ->
                      Tab
              end
      end,
      Tab,
      Forms).

-spec create_ref_tuple(tuple(), string(), arity()) -> tuple().
create_ref_tuple({ref}, Name, Arity) ->
    {ref, Name, Arity};
create_ref_tuple({qref, Module}, Name, Arity) ->
    {qref, Module, Name, Arity}.

-spec extend_symtab_with_module_list(symtab:t(), cmd_opts(), [atom()]) -> symtab:t().
extend_symtab_with_module_list(Symtab, Opts, Modules) ->
    traverse_module_list(paths:find_search_paths(Opts), Symtab, Modules).

traverse_module_list(SearchPaths, Symtab, Modules) ->
    case Modules of
        [CurrentModule | RemainingModules] ->
            {SourcePath, IncludePath} = find_module_path(SearchPaths, CurrentModule),
            ?LOG_NOTE("Path to includes ~s", IncludePath),

            RawForms = parse:parse_file_or_die(SourcePath, #parse_opts{ verbose = false, includes = [IncludePath] }),
            Forms = ast_transform:trans(SourcePath, RawForms),

            NewSymtab = symtab:extend_symtab(Forms, CurrentModule, Symtab),
            traverse_module_list(SearchPaths, NewSymtab, RemainingModules);
        [] ->
            Symtab
    end.

-spec find_module_path([file:filename()], atom()) -> {file:filename(), file:filename()}.
find_module_path(SearchPaths, Module) ->
    Filename = string:concat(atom_to_list(Module), ".erl"),
    ?LOG_NOTE("Looking for file ~s", Filename),
    {value, Result} = lists:search(
      fun(Path) ->
              SourcePath = filename:join([Path, "src"]),
              case filelib:find_file(Filename, SourcePath) of
                  {ok, _} -> true;
                  {error, not_found} -> false
              end
      end, SearchPaths),
    IncludePath = filename:join([Result, "include"]),
    {filename:join([Result, "src", Filename]), IncludePath}.
