-module(cm_depgraph).

% @doc This module implements a data structure that maintains a graph of the dependencies
% of erlang modules. The relationship is inverted, so if a module A is using a resource
% from module B then this will be represented in the graph as B -> A.
% The graph currently records only dependencies between modules local to the project. Hence,
% if an external dependency changes, you have to delete the index.

-include("log.hrl").

-export([
    new/0, new/1,
    find_dependent_files/2,
    all_sources/1,
    build_dep_graph/2,
    refresh/3,
    pretty_depgraph/1,
    save_depgraph/3,
    load_depgraph/2
]).

-export_type([dep_graph/0]).

-ifdef(TEST).
-export([
    add_dependency/3,
    update_dep_graph/4
]).
-endif.

-include("etylizer.hrl").

-type dep_graph() :: {
    sets:set(file:filename()),
    % Maps a file F to all files that F directly or indirectly depends on.
    #{file:filename() => sets:set(file:filename())},
    % Separate mapping module name -> module names, always in sync with the mapping
    % filename -> filenames.
    #{atom() => sets:set(atom())}
}.

-spec new() -> dep_graph().
new() -> {sets:new([{version, 2}]), maps:new(), maps:new()}.

-spec new([file:filename()]) -> dep_graph().
new(Srcs) ->
    lists:foldl(fun add_file/2, new(), Srcs).

-spec pretty_depgraph(dep_graph()) ->
    {[file:filename()], #{file:filename() => [file:filename()]}}.
pretty_depgraph({Srcs, DepFiles, _}) ->
    {sets:to_list(Srcs), maps:map(fun(_, V) -> sets:to_list(V) end, DepFiles)}.

-spec all_sources(dep_graph()) -> [file:filename()].
all_sources({Srcs, _, _}) -> sets:to_list(Srcs).

% Checks whether M1 is a dependency of M2
-spec has_rev_dep(atom(), atom(), dep_graph()) -> boolean().
has_rev_dep(M1, M2, {_, _, DepMod}) ->
    case maps:get(M1, DepMod, not_found) of
        not_found -> false;
        Mods -> sets:is_element(M2, Mods)
    end.

% Given a filename F, find all files that use something from F.
-spec find_dependent_files(file:filename(), dep_graph()) -> [file:filename()].
find_dependent_files(Path, {_, DepFiles, _}) ->
    PathNorm = utils:normalize_path(Path),
    case maps:find(PathNorm, DepFiles) of
        error -> [];
        {ok, Files} -> sets:to_list(Files)
    end.

-spec add_dependency(file:filename(), file:filename(), dep_graph()) -> dep_graph().
add_dependency(Path, Dep, {Srcs, DepFiles, DepMods}) ->
    PathNorm = utils:normalize_path(Path),
    PathMod = ast_utils:modname_from_path(PathNorm),
    DepNorm = utils:normalize_path(Dep),
    DepMod = ast_utils:modname_from_path(Dep),
    Deps1 = maps:get(PathNorm, DepFiles, sets:new([{version, 2}])),
    Deps2 = maps:get(PathNorm, DepMods, sets:new([{version, 2}])),
    NewDepFiles = maps:put(PathNorm, sets:add_element(DepNorm, Deps1), DepFiles),
    NewDepMods = maps:put(PathMod, sets:add_element(DepMod, Deps2), DepMods),
    NewSrcs = sets:add_element(PathNorm, sets:add_element(DepNorm, Srcs)),
    {NewSrcs, NewDepFiles, NewDepMods}.

-spec add_file(file:filename(), dep_graph()) -> dep_graph().
add_file(Path, {Srcs, DepFiles, DepMods}) ->
    PathNorm = utils:normalize_path(Path),
    NewSrcs = sets:add_element(PathNorm, Srcs),
    {NewSrcs, DepFiles, DepMods}.

% Replaces the dependencies of the given files by the ones of their current content.
-spec refresh([file:filename()], paths:search_path(), dep_graph()) -> dep_graph().
refresh(Files, SearchPath, DepGraph) ->
    lists:foldl(
        fun(F, G) -> update_dep_graph(F, parse_intern(F), SearchPath, remove_dependent(F, G)) end,
        DepGraph, Files).

% Removes a file from all sets of dependent files.
-spec remove_dependent(file:filename(), dep_graph()) -> dep_graph().
remove_dependent(Path, {Srcs, DepFiles, DepMods}) ->
    PathNorm = utils:normalize_path(Path),
    PathMod = ast_utils:modname_from_path(PathNorm),
    NewDepFiles = maps:map(
        fun(_, Deps) -> sets:del_element(PathNorm, Deps) end, DepFiles),
    NewDepMods = maps:map(
        fun(_, Deps) -> sets:del_element(PathMod, Deps) end, DepMods),
    {Srcs, NewDepFiles, NewDepMods}.

% Cache for type-reference lookups, keyed by source path.
-type type_refs_cache() :: #{file:filename() => [ast:mod_name()]}.

-spec update_dep_graph(
    file:filename(),
    ast:forms(),
    paths:search_path(),
    dep_graph()
) -> dep_graph().
update_dep_graph(Path, Forms, SearchPath, DepGraph) ->
    Modules = ast_utils:referenced_modules(Forms),
    ?LOG_DEBUG("Modules referenced from ~p: ~p", Path, Modules),
    {Result, _} = traverse_module_list(
        Path, Modules, SearchPath, add_file(Path, DepGraph), maps:new()),
    Result.

-spec traverse_module_list(
    file:filename(),
    [atom()],
    paths:search_path(),
    dep_graph(),
    type_refs_cache()
) -> {dep_graph(), type_refs_cache()}.
traverse_module_list(_, [], _, DepGraph, Cache) ->
    {DepGraph, Cache};
traverse_module_list(Path, [CurrentModule | RemainingModules], SearchPath, DepGraph, Cache) ->
    case find_source_for_module(CurrentModule, SearchPath) of
        false ->
            traverse_module_list(Path, RemainingModules, SearchPath, DepGraph, Cache);
        SourcePath ->
            NewDepGraph = add_dependency(SourcePath, Path, DepGraph),
            {TypeRefs, NewCache} = cached_type_refs(SourcePath, Cache),
            PathMod = ast_utils:modname_from_path(Path),
            AdditionalModules =
                lists:filter(
                    fun (ModName) -> not has_rev_dep(ModName, PathMod, DepGraph) end,
                    TypeRefs
                ),
            ?LOG_DEBUG("Additional modules for path ~s (current: ~w): ~200p", Path, CurrentModule, AdditionalModules),
            traverse_module_list(Path, RemainingModules ++ AdditionalModules,
                SearchPath, NewDepGraph, NewCache)
    end.

% @doc Returns referenced_modules_via_types for a source file, cached per path.
-spec cached_type_refs(file:filename(), type_refs_cache()) ->
    {[ast:mod_name()], type_refs_cache()}.
cached_type_refs(SourcePath, Cache) ->
    case maps:find(SourcePath, Cache) of
        {ok, Result} ->
            {Result, Cache};
        error ->
            Forms = parse_intern(SourcePath),
            Result = ast_utils:referenced_modules_via_types(Forms),
            {Result, maps:put(SourcePath, Result, Cache)}
    end.

-spec find_source_for_module(atom(), paths:search_path()) -> false | file:filename().
find_source_for_module(Module, SearchPath) ->
    % A referenced module may be unresolvable (e.g. an Elixir stdlib module that
    % is not on the search path). Treat that as "no local source" instead of
    % aborting, so dependency analysis can proceed.
    try paths:find_module_path(SearchPath, Module) of
        {local, Src, _} -> Src;
        _ -> false
    catch
        throw:{etylizer, name_error, _} -> false
    end.

% Builds the dependency graph.
-spec build_dep_graph([file:filename()], paths:search_path()) -> dep_graph().
build_dep_graph(Files, SearchPath) ->
    build_dep_graph(lists:map(fun utils:normalize_path/1, Files),
        SearchPath, new(), sets:new([{version, 2}]), maps:new()).

-spec build_dep_graph(
        [file:filename()],
        paths:search_path(),
        dep_graph(),
        sets:set(file:filename()),
        type_refs_cache()
    ) -> dep_graph().
build_dep_graph(Worklist, SearchPath, DepGraph, AlreadyHandled, Cache) ->
    case Worklist of
        [] -> DepGraph;
        [File | Rest] ->
            ?LOG_DEBUG("Adding ~p to dependency graph", File),
            Forms = parse_intern(File),
            Modules = ast_utils:referenced_modules(Forms),
            ?LOG_DEBUG("Modules referenced from ~p: ~p", File, Modules),
            {NewDepGraph0, NewCache} = traverse_module_list(
                File, Modules, SearchPath, add_file(File, DepGraph), Cache),
            {All, _, _} = NewDepGraph = ?assert_type(NewDepGraph0, dep_graph()),
            NewAlreadyHandled = sets:add_element(File, AlreadyHandled),
            NewFiles = sets:subtract(
                sets:subtract(All, NewAlreadyHandled),
                sets:from_list(Rest, [{version, 2}])
            ),
            ?LOG_TRACE("Done adding ~p to dependency graph", File),
            build_dep_graph(
                Rest ++ lists:map(fun utils:normalize_path/1, sets:to_list(NewFiles)),
                SearchPath,
                NewDepGraph, NewAlreadyHandled, NewCache)
    end.


-define(DEPGRAPH_VERSION, 2).

% Saves the graph together with the entry points it was built from.
-spec save_depgraph(file:filename(), [file:filename()], dep_graph()) -> ok.
save_depgraph(Path, EntryPoints, DepGraph) ->
    filelib:ensure_dir(Path),
    Stored = {etylizer_depgraph, ?DEPGRAPH_VERSION, lists:sort(EntryPoints), DepGraph},
    Formatted = lists:flatten(io_lib:format("~p.~n", [Stored])),
    case file:write_file(Path, ?assert_type(Formatted, string())) of
        ok -> ok;
        Error -> ?LOG_WARN("Could not save the dependency graph at ~p: ~p", Path, Error)
    end.

% The graph saved at Path, unless it was built from other entry points.
-spec load_depgraph(file:filename(), [file:filename()]) -> {ok, dep_graph()} | stale.
load_depgraph(Path, EntryPoints) ->
    Expected = lists:sort(EntryPoints),
    case file:consult(Path) of
        {ok, [{etylizer_depgraph, ?DEPGRAPH_VERSION, Expected, DepGraph}]} ->
            {ok, ?assert_type(DepGraph, dep_graph())};
        _ ->
            ?LOG_DEBUG("No dependency graph for the entry points at ~p", Path),
            stale
    end.

-spec parse_intern(file:filename()) -> [ast:form()].
parse_intern(P) -> parse_cache:parse(intern, P).
