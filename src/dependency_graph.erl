-module(dependency_graph).
-export([find_dependencies/2, add_dependency/3, update_dependency_graph/4]).

-spec find_dependencies(file:filename(), map()) -> [file:filename()].
find_dependencies(Path, DependencyGraph) ->
    case maps:find(Path, DependencyGraph) of
        error -> [];
        {ok, Files} -> Files
    end.

-spec add_dependency(file:filename(), file:filename(), map()) -> map().
add_dependency(Path, Dependency, DependencyGraph) ->
    Dependencies = find_dependencies(Path, DependencyGraph),
    maps:put(Path, [Dependency | Dependencies], DependencyGraph).

-spec update_dependency_graph(file:filename(), ast:forms(), [file:filename()], map()) -> map().
update_dependency_graph(Path, Forms, SourcesList, DependencyGraph) ->
    Modules = ast_utils:export_modules(Forms),
    traverse_module_list(Path, Modules, SourcesList, DependencyGraph).

-spec traverse_module_list(file:filename(), [atom()], [file:filename()], map()) -> map().
traverse_module_list(Path, Modules, SourcesList, DependencyGraph) ->
    case Modules of
        [CurrentModule | RemainingModules] ->
            case find_source_for_module(CurrentModule, SourcesList) of
                false ->
                    traverse_module_list(Path, RemainingModules, SourcesList, DependencyGraph);
                {value, SourcePath} ->
                    NewDependencyGraph = add_dependency(SourcePath, Path, DependencyGraph),
                    traverse_module_list(Path, RemainingModules, SourcesList, NewDependencyGraph)
            end;
        [] ->
            DependencyGraph
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
