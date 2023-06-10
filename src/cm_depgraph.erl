-module(cm_depgraph).

% @doc This module implements a data structure that maintains a graph of the dependencies
% of erlang modules. The relationship is inverted, so if a module A is using a resource
% from module B then this will be represented in the graph as B -> A.

-export([find_dependent_files/2, add_dependency/3, update_dependency_graph/4]).

-export_type([dependency_graph/0]).

-type dependency_graph() :: #{file:filename() => [file:filename()]}.

-spec find_dependent_files(file:filename(), dependency_graph()) -> [file:filename()].
find_dependent_files(Path, DependencyGraph) ->
    case maps:find(Path, DependencyGraph) of
        error -> [];
        {ok, Files} -> Files
    end.

-spec add_dependency(file:filename(), file:filename(), dependency_graph()) -> dependency_graph().
add_dependency(Path, Dependency, DependencyGraph) ->
    Dependencies = find_dependent_files(Path, DependencyGraph),
    maps:put(Path, [Dependency | Dependencies], DependencyGraph).

-spec update_dependency_graph(file:filename(), ast:forms(), [file:filename()], dependency_graph()) -> dependency_graph().
update_dependency_graph(Path, Forms, SourcesList, DependencyGraph) ->
    Modules = ast_utils:export_modules(Forms),
    traverse_module_list(Path, Modules, SourcesList, DependencyGraph).

-spec traverse_module_list(file:filename(), [atom()], [file:filename()], dependency_graph()) -> dependency_graph().
traverse_module_list(_, [], _, DependencyGraph) ->
    DependencyGraph;

traverse_module_list(Path, [CurrentModule | RemainingModules], SourcesList, DependencyGraph) ->
    case find_source_for_module(CurrentModule, SourcesList) of
        false ->
            traverse_module_list(Path, RemainingModules, SourcesList, DependencyGraph);
        {value, SourcePath} ->
            NewDependencyGraph = add_dependency(SourcePath, Path, DependencyGraph),
            traverse_module_list(Path, RemainingModules, SourcesList, NewDependencyGraph)
    end.

-spec find_source_for_module(atom(), [file:filename()]) -> boolean() | tuple().
find_source_for_module(Module, SourcesList) ->
    ModuleFile = string:concat(atom_to_list(Module), ".erl"),
    lists:search(
      fun(SourceFile) ->
              case string:find(SourceFile, ModuleFile) of
                  nomatch -> false;
                  _ -> true
              end
      end, SourcesList).
