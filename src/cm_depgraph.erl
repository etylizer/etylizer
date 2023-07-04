-module(cm_depgraph).

% @doc This module implements a data structure that maintains a graph of the dependencies
% of erlang modules. The relationship is inverted, so if a module A is using a resource
% from module B then this will be represented in the graph as B -> A.
% The graph currently records only dependencies between modules local to the project. Hence,
% if an external dependency changes, you have to delete the index.

-include_lib("log.hrl").

-export([
    new/0,
    find_dependent_files/2,
    all_sources/1,
    add_dependency/3,
    update_dep_graph/4,
    build_dep_graph/3,
    pretty_depgraph/1
]).

-export_type([dep_graph/0]).

-type dep_graph() :: {
    sets:set(file:filename()),
    #{file:filename() => sets:set(file:filename())}
}.

-spec new() -> dep_graph().
new() -> {sets:new(), maps:new()}.

-spec pretty_depgraph(dep_graph()) ->
    {[file:filename()], #{file:filename() => [file:filename()]}}.
pretty_depgraph({Srcs, DepGraph}) ->
    {sets:to_list(Srcs), maps:map(fun(_, V) -> sets:to_list(V) end, DepGraph)}.

-spec all_sources(dep_graph()) -> [file:filename()].
all_sources({Srcs, _}) -> sets:to_list(Srcs).

% Given a filename F, find all files that use something from F.
-spec find_dependent_files(file:filename(), dep_graph()) -> [file:filename()].
find_dependent_files(Path, {_, DepGraph}) ->
    PathNorm = normalize(Path),
    case maps:find(PathNorm, DepGraph) of
        error -> [];
        {ok, Files} -> sets:to_list(Files)
    end.

-spec normalize(file:filename()) -> file:filename().
normalize(P) -> filename:nativename(P).

-spec add_dependency(file:filename(), file:filename(), dep_graph()) -> dep_graph().
add_dependency(Path, Dep, {Srcs, DepGraph}) ->
    PathNorm = normalize(Path),
    DepNorm = normalize(Dep),
    Deps =
        case maps:find(PathNorm, DepGraph) of
            error -> sets:new();
            {ok, Files} -> Files
        end,
    NewDepGraph = maps:put(PathNorm, sets:add_element(DepNorm, Deps), DepGraph),
    NewSrcs = sets:add_element(PathNorm, sets:add_element(DepNorm, Srcs)),
    {NewSrcs, NewDepGraph}.

-spec update_dep_graph(file:filename(), ast:forms(), paths:search_path(), dep_graph()) -> dep_graph().
update_dep_graph(Path, Forms, SearchPath, DepGraph) ->
    Modules = ast_utils:referenced_modules(Forms),
    ?LOG_DEBUG("Modules reference from ~p: ~p", Path, Modules),
    traverse_module_list(Path, Modules, SearchPath, DepGraph).

-spec traverse_module_list(file:filename(), [atom()], paths:search_path(), dep_graph()) -> dep_graph().
traverse_module_list(_, [], _, DepGraph) ->
    DepGraph;
traverse_module_list(Path, [CurrentModule | RemainingModules], SearchPath, DepGraph) ->
    case find_source_for_module(CurrentModule, SearchPath) of
        false ->
            traverse_module_list(Path, RemainingModules, SearchPath, DepGraph);
        SourcePath ->
            NewDepGraph = add_dependency(SourcePath, Path, DepGraph),
            traverse_module_list(Path, RemainingModules, SearchPath, NewDepGraph)
    end.

-spec find_source_for_module(atom(), paths:search_path()) -> false | file:filename().
find_source_for_module(Module, SearchPath) ->
    Entry = paths:find_module_path(SearchPath, Module),
    case Entry of
        {local, Src, _} -> Src;
        _ -> false
    end.

% Builds the dependency graph.
-spec build_dep_graph(
    [file:filename()], paths:search_path(), fun((file:filename()) -> [ast:forms()]))
    -> {dep_graph(), file:filename()}.
build_dep_graph(Files, SearchPath, ParseFun) ->
    build_dep_graph(lists:map(fun normalize/1, Files),
        SearchPath, ParseFun, new(), sets:new()).

-spec build_dep_graph(
        [file:filename()],
        paths:search_path(),
        fun((file:filename()) -> [ast:forms()]),
        dep_graph(),
        sets:set(file:filename())
    ) -> {dep_graph(), file:filename()}.
build_dep_graph(Worklist, SearchPath, ParseFun, DepGraph, AlreadyHandled) ->
    case Worklist of
        [] -> DepGraph;
        [File | Rest] ->
            Forms = ParseFun(File),
            {All, _} = NewDepGraph = update_dep_graph(File, Forms, SearchPath, DepGraph),
            ?LOG_DEBUG("Dependecy graph after processing ~p: ~p", File,
                cm_depgraph:pretty_depgraph(NewDepGraph)),
            NewFiles = sets:subtract(All, AlreadyHandled),
            build_dep_graph(
                Rest ++ sets:to_list(NewFiles), SearchPath, ParseFun,
                NewDepGraph, sets:add_element(File, AlreadyHandled))
    end.
