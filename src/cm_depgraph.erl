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
    update_dep_graph/4,
    remove_dependent/2,
    pretty_depgraph/1,
    save_depgraph/2,
    load_depgraph/2,
    build_fun_dep_graph/1,
    update_fun_dep_graph/3,
    find_fun_callers/2,
    save_fun_depgraph/2,
    load_fun_depgraph/1
]).

-export_type([dep_graph/0, fun_dep_graph/0]).

-ifdef(TEST).
-export([
    add_dependency/3
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

% @doc Remove a file from all reverse-dependency value sets.
% Used for incremental updates: remove old edges before re-analyzing.
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
    Entry = paths:find_module_path(SearchPath, Module),
    case Entry of
        {local, Src, _} -> Src;
        _ -> false
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


-define(DEPGRAPH_VERSION, 1).

% @doc Save the dependency graph to disk.
-spec save_depgraph(file:filename(), dep_graph()) -> ok.
save_depgraph(Path, DepGraph) ->
    filelib:ensure_dir(Path),
    {Srcs, DepFiles, DepMods} = DepGraph,
    Serializable = {sets:to_list(Srcs),
        maps:map(fun(_, V) -> sets:to_list(V) end, DepFiles),
        maps:map(fun(_, V) -> sets:to_list(V) end, DepMods)},
    Formatted = lists:flatten(
        io_lib:format("~p.~n", [{etylizer_depgraph, ?DEPGRAPH_VERSION, Serializable}])),
    ?assert_pattern(ok, file:write_file(Path, Formatted)).

% @doc Load the dependency graph from disk.
-spec load_depgraph(file:filename(), [file:filename()]) -> {ok, dep_graph()} | stale.
load_depgraph(Path, ExpectedSources) ->
    case filelib:is_file(Path) of
        false ->
            ?LOG_DEBUG("No cached dependency graph at ~p", Path),
            stale;
        true ->
            case file:consult(Path) of
                {ok, [{etylizer_depgraph, ?DEPGRAPH_VERSION, {SrcList, DepFilesMap0, DepModsMap0}}]} ->
                    Srcs = sets:from_list(?assert_type(SrcList, [file:filename()]), [{version, 2}]),
                    ExpectedSet = sets:from_list(
                        lists:map(fun utils:normalize_path/1, ExpectedSources),
                        [{version, 2}]),
                    DepFilesMap = ?assert_type(DepFilesMap0, #{file:filename() => [file:filename()]}),
                    DepModsMap = ?assert_type(DepModsMap0, #{atom() => [atom()]}),
                    case sets:is_equal(Srcs, ExpectedSet) of
                        true ->
                            ?LOG_TRACE("Loaded cached dependency graph from ~p", Path),
                            DepFiles = maps:map(
                                fun(_, V) -> sets:from_list(V, [{version, 2}]) end, DepFilesMap),
                            DepMods = maps:map(
                                fun(_, V) -> sets:from_list(V, [{version, 2}]) end, DepModsMap),
                            {ok, {Srcs, DepFiles, DepMods}};
                        false ->
                            ?LOG_DEBUG("Cached dependency graph is stale (source set changed)"),
                            stale
                    end;
                _ ->
                    ?LOG_WARN("Cached dependency graph at ~p has unexpected format", Path),
                    stale
            end
    end.

-spec parse_intern(file:filename()) -> [ast:form()].
parse_intern(P) -> parse_cache:parse(intern, P).

%%% Function-level dependency graph

% Reverse deps: fun_id -> set of callers of that function
-type fun_dep_graph() :: #{cm_fun_deps:fun_id() => sets:set(cm_fun_deps:fun_id())}.

% @doc Build function-level reverse dependency graph from module analyses.
% If function f calls function g, we store g -> f (reverse dependency).
-spec build_fun_dep_graph([{file:filename(), cm_fun_deps:module_info()}]) -> fun_dep_graph().
build_fun_dep_graph(ModInfos) ->
    lists:foldl(
        fun(Entry, Graph) -> add_module_to_fun_dep_graph(Entry, Graph) end,
        ?assert_type(maps:new(), fun_dep_graph()), ModInfos).

% @doc Add a single module's function calls to the reverse dependency graph.
-spec add_module_to_fun_dep_graph(
    {file:filename(), cm_fun_deps:module_info()}, fun_dep_graph()) -> fun_dep_graph().
add_module_to_fun_dep_graph({_File, ModInfo}, Graph) ->
    Funs = ?assert_type(maps:get(funs, ModInfo), #{cm_fun_deps:fun_id() => cm_fun_deps:fun_info()}),
    maps:fold(
        fun(CallerId, FunInfo, G) ->
            Calls = ?assert_type(maps:get(calls, FunInfo), [cm_fun_deps:fun_id()]),
            lists:foldl(
                fun(CalleeId, G2) ->
                    Existing = maps:get(CalleeId, G2, sets:new([{version, 2}])),
                    maps:put(CalleeId, sets:add_element(CallerId, Existing), G2)
                end, G, Calls)
        end, Graph, Funs).

% @doc Incrementally update the function dep graph: remove all edges involving
% changed modules, then add back edges from re-analyzed module infos.
-spec update_fun_dep_graph(
    fun_dep_graph(), sets:set(atom()),
    [{file:filename(), cm_fun_deps:module_info()}]) -> fun_dep_graph().
update_fun_dep_graph(Graph, ChangedMods, NewModInfos) ->
    PrunedGraph = prune_fun_dep_graph(Graph, ChangedMods),
    lists:foldl(
        fun(Entry, G) -> add_module_to_fun_dep_graph(Entry, G) end,
        PrunedGraph, NewModInfos).

% @doc Remove all edges involving modules in the given set.
-spec prune_fun_dep_graph(fun_dep_graph(), sets:set(atom())) -> fun_dep_graph().
prune_fun_dep_graph(Graph, ChangedMods) ->
    maps:filtermap(
        fun({CalleeMod, _, _}, CallerSet) ->
            case sets:is_element(CalleeMod, ChangedMods) of
                true -> false;
                false ->
                    NewCallerSet = sets:filter(
                        fun({CallerMod, _, _}) ->
                            not sets:is_element(CallerMod, ChangedMods)
                        end, CallerSet),
                    {true, NewCallerSet}
            end
        end, Graph).

% @doc Find all direct callers of a given function.
-spec find_fun_callers(cm_fun_deps:fun_id(), fun_dep_graph()) -> [cm_fun_deps:fun_id()].
find_fun_callers(FunId, Graph) ->
    case maps:find(FunId, Graph) of
        error -> [];
        {ok, Callers} -> sets:to_list(Callers)
    end.

-define(FUN_DEPGRAPH_VERSION, 1).

% @doc Save the function-level dependency graph to disk.
-spec save_fun_depgraph(file:filename(), fun_dep_graph()) -> ok.
save_fun_depgraph(Path, Graph) ->
    filelib:ensure_dir(Path),
    Serializable = maps:map(fun(_, V) -> sets:to_list(V) end, Graph),
    Formatted = lists:flatten(
        io_lib:format("~p.~n", [{etylizer_fun_depgraph, ?FUN_DEPGRAPH_VERSION, Serializable}])),
    ?assert_pattern(ok, file:write_file(Path, Formatted)).

% @doc Load the function-level dependency graph from disk.
-spec load_fun_depgraph(file:filename()) -> {ok, fun_dep_graph()} | stale.
load_fun_depgraph(Path) ->
    case filelib:is_file(Path) of
        false ->
            ?LOG_DEBUG("No cached function dependency graph at ~p", Path),
            stale;
        true ->
            case file:consult(Path) of
                {ok, [{etylizer_fun_depgraph, ?FUN_DEPGRAPH_VERSION, SerMap0}]} ->
                    ?LOG_TRACE("Loaded cached function dependency graph from ~p", Path),
                    SerMap = ?assert_type(SerMap0, #{cm_fun_deps:fun_id() => [cm_fun_deps:fun_id()]}),
                    Graph = maps:map(
                        fun(_, V) -> sets:from_list(V, [{version, 2}]) end, SerMap),
                    {ok, Graph};
                _ ->
                    ?LOG_WARN("Cached function dep graph at ~p has unexpected format", Path),
                    stale
            end
    end.
