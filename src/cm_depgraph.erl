-module(cm_depgraph).

% @doc This module implements a data structure that maintains a graph of the dependencies
% of erlang modules. The relationship is inverted, so if a module A is using a resource
% from module B then this will be represented in the graph as B -> A.
% The graph currently records only dependencies between modules local to the project. Hence,
% if an external dependency changes, you have to delete the index.

-include_lib("kernel/include/logger.hrl").

-export([
    new/0, new/1,
    find_dependent_files/2,
    all_sources/1,
    build_dep_graph/2,
    pretty_depgraph/1
]).

-export_type([dep_graph/0]).

-ifdef(TEST).
-export([
    add_dependency/3,
    update_dep_graph/4
]).
-endif.


-type dep_graph() :: {
    sets:set(file:filename()),
    % Maps a file F to all files that F directly or indirectly depends on.
    #{file:filename() => {sets:set(file:filename())}},
    % Separate mapping module name -> module names, always in sync with the mapping
    % filename -> filenames.
    #{atom() => {sets:set(atom())}}
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

-spec update_dep_graph(
    file:filename(),
    ast:forms(),
    paths:search_path(),
    dep_graph()
) -> dep_graph().
update_dep_graph(Path, Forms, SearchPath, DepGraph) ->
    Modules = ast_utils:referenced_modules(Forms),
    ?LOG_DEBUG("Modules referenced from ~p: ~p", [Path, Modules]),
    traverse_module_list(Path, Modules, SearchPath, add_file(Path, DepGraph)).

-spec traverse_module_list(
    file:filename(),
    [atom()],
    paths:search_path(),
    dep_graph()
) -> dep_graph().
traverse_module_list(_, [], _, DepGraph) ->
    DepGraph;
traverse_module_list(Path, [CurrentModule | RemainingModules], SearchPath, DepGraph) ->
    case find_source_for_module(CurrentModule, SearchPath) of
        false ->
            traverse_module_list(Path, RemainingModules, SearchPath, DepGraph);
        SourcePath ->
            NewDepGraph = add_dependency(SourcePath, Path, DepGraph),
            Forms = parse_intern(SourcePath),
            PathMod = ast_utils:modname_from_path(Path),
            AdditionalModules =
                lists:filter(
                    fun (ModName) -> not has_rev_dep(ModName, PathMod, DepGraph) end,
                    ast_utils:referenced_modules_via_types(Forms)
                ),
            ?LOG_DEBUG("Additional modules for path ~s (current: ~w): ~200p", 
                       [Path, CurrentModule, AdditionalModules]),
            traverse_module_list(Path, RemainingModules ++ AdditionalModules,
                SearchPath, NewDepGraph)
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
        SearchPath, new(), sets:new([{version, 2}])).

-spec build_dep_graph(
        [file:filename()],
        paths:search_path(),
        dep_graph(),
        sets:set(file:filename())
    ) -> dep_graph().
build_dep_graph(Worklist, SearchPath, DepGraph, AlreadyHandled) ->
    case Worklist of
        [] -> DepGraph;
        [File | Rest] ->
            ?LOG_INFO("Adding ~p to dependency graph", [File]),
            Forms = parse_intern(File),
            {All, _, _} = NewDepGraph = update_dep_graph(File, Forms, SearchPath, DepGraph),
            NewAlreadyHandled = sets:add_element(File, AlreadyHandled),
            NewFiles = sets:subtract(
                sets:subtract(All, NewAlreadyHandled),
                sets:from_list(Rest, [{version, 2}])
            ),
            ?LOG_INFO("Done adding ~p to dependency graph", [File]),
            build_dep_graph(
                Rest ++ lists:map(fun utils:normalize_path/1, sets:to_list(NewFiles)),
                SearchPath,
                NewDepGraph, NewAlreadyHandled)
    end.


-spec parse_intern(file:filename()) -> [ast:form()].
parse_intern(P) -> parse_cache:parse(intern, P).
