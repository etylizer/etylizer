-module(cm_depgraph).

% @doc This module implements a data structure that maintains a graph of the dependencies
% of erlang modules. The relationship is inverted, so if a module A is using a resource
% from module B then this will be represented in the graph as B -> A.
% The graph currently records only dependencies between modules local to the project. Hence,
% if an external dependency changes, you have to delete the index.

-include("log.hrl").
-include("etylizer_main.hrl").

-export([
    new/0, new/1,
    find_dependent_files/2,
    all_sources/1,
    cached/3,
    pretty_depgraph/1
]).

-export_type([dep_graph/0]).

-ifdef(TEST).
-export([
    add_dependency/3,
    update_dep_graph/4,
    load_depgraph/2
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
    Deps2 = maps:get(PathMod, DepMods, sets:new([{version, 2}])),
    NewDepFiles = maps:put(PathNorm, sets:add_element(DepNorm, Deps1), DepFiles),
    NewDepMods = maps:put(PathMod, sets:add_element(DepMod, Deps2), DepMods),
    NewSrcs = sets:add_element(PathNorm, sets:add_element(DepNorm, Srcs)),
    {NewSrcs, NewDepFiles, NewDepMods}.

-spec add_file(file:filename(), dep_graph()) -> dep_graph().
add_file(Path, {Srcs, DepFiles, DepMods}) ->
    PathNorm = utils:normalize_path(Path),
    NewSrcs = sets:add_element(PathNorm, Srcs),
    {NewSrcs, DepFiles, DepMods}.

-spec refresh([file:filename()], paths:search_path(), dep_graph()) -> dep_graph().
refresh(Changed, SearchPath, DepGraph = {Srcs, _, _}) ->
    Files = lists:usort(lists:flatmap(
        fun(F) -> [utils:normalize_path(F) | find_dependent_files(F, DepGraph)] end, Changed)),
    Others = sets:subtract(Srcs, sets:from_list(Files, [{version, 2}])),
    build_dep_graph(Files, SearchPath, lists:foldl(fun remove_dependent/2, DepGraph, Files), Others).

-spec remove_dependent(file:filename(), dep_graph()) -> dep_graph().
remove_dependent(Path, {Srcs, DepFiles, DepMods}) ->
    PathNorm = utils:normalize_path(Path),
    PathMod = ast_utils:modname_from_path(PathNorm),
    NewDepFiles = maps:map(
        fun(_, Deps) -> sets:del_element(PathNorm, Deps) end, DepFiles),
    NewDepMods = maps:map(
        fun(_, Deps) -> sets:del_element(PathMod, Deps) end, DepMods),
    {Srcs, NewDepFiles, NewDepMods}.

-spec update_dep_graph(
    file:filename(),
    ast:forms(),
    paths:search_path(),
    dep_graph()
) -> dep_graph().
update_dep_graph(Path, Forms, SearchPath, DepGraph) ->
    Modules = ast_utils:referenced_modules(Forms),
    ?LOG_DEBUG("Modules referenced from ~p: ~p", Path, Modules),
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
            PathMod = ast_utils:modname_from_path(Path),
            AdditionalModules =
                lists:filter(
                    fun (ModName) -> not has_rev_dep(ModName, PathMod, DepGraph) end,
                    type_refs(SourcePath)
                ),
            ?LOG_DEBUG("Additional modules for path ~s (current: ~w): ~200p", Path, CurrentModule, AdditionalModules),
            traverse_module_list(Path, RemainingModules ++ AdditionalModules,
                SearchPath, NewDepGraph)
    end.

-spec type_refs(file:filename()) -> [ast:mod_name()].
type_refs(Path) ->
    symtab_cache:cached({type_refs, Path}, fun() ->
        Forms = parse_intern(Path),
        {ast_utils:referenced_modules_via_types(Forms), [Path | parse_cache:headers(Path)]}
    end).

-spec find_source_for_module(atom(), paths:search_path()) -> false | file:filename().
find_source_for_module(Module, SearchPath) ->
    Entry = paths:find_module_path(SearchPath, Module),
    case Entry of
        {local, Src, _} -> Src;
        _ -> false
    end.

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
            ?LOG_DEBUG("Adding ~p to dependency graph", File),
            Forms = parse_intern(File),
            {All, _, _} = NewDepGraph = update_dep_graph(File, Forms, SearchPath, DepGraph),
            NewAlreadyHandled = sets:add_element(File, AlreadyHandled),
            NewFiles = sets:subtract(
                sets:subtract(All, NewAlreadyHandled),
                sets:from_list(Rest, [{version, 2}])
            ),
            ?LOG_TRACE("Done adding ~p to dependency graph", File),
            build_dep_graph(
                Rest ++ lists:map(fun utils:normalize_path/1, sets:to_list(NewFiles)),
                SearchPath,
                NewDepGraph, NewAlreadyHandled)
    end.

-spec cached([file:filename()], paths:search_path(), cmd_opts()) -> dep_graph().
cached(SourceList, SearchPath, Opts) ->
    File = paths:depgraph_file_name(Opts),
    Key = {lists:sort(SourceList), SearchPath, symtab_cache:stamp(Opts)},
    Loaded = case Opts#opts.force of
                 true -> stale;
                 false -> load_depgraph(File, Key)
             end,
    {Old, Changed, Kept} = case Loaded of
                               {ok, G0, Cs, Ks} -> {G0, Cs, Ks};
                               stale -> {new(), SourceList, #{}}
                           end,
    ?LOG_DEBUG("Updating the dependency graph for ~p", Changed),
    G = refresh(Changed, SearchPath, Old),
    case Changed of [] -> ok; _ -> save_depgraph(File, Key, G, Kept) end,
    G.

-define(DEPGRAPH_VERSION, 4).

% Kept are the hashes of the unchanged sources, the others were parsed in this run.
-spec save_depgraph(file:filename(), term(), dep_graph(), #{file:filename() => hashes()}) -> ok.
save_depgraph(Path, Key, DepGraph, Kept) ->
    filelib:ensure_dir(Path),
    Hashes = [case maps:find(F, Kept) of
                  {ok, Hs} -> {F, Hs};
                  error -> {F, hashes([F | parse_cache:headers(F)])}
              end || F <- lists:sort(all_sources(DepGraph))],
    Stored = {etylizer_depgraph, ?DEPGRAPH_VERSION, Key, Hashes, DepGraph},
    Formatted = lists:flatten(io_lib:format("~p.~n", [Stored])),
    case file:write_file(Path, ?assert_type(Formatted, string())) of
        ok -> ok;
        Error -> ?LOG_WARN("Could not save the dependency graph at ~p: ~p", Path, Error)
    end.

% stale if there is none for Key or one of its sources is gone. A source changed when it or
% a header it includes changed. Also returns the hashes of the unchanged sources.
-spec load_depgraph(file:filename(), term()) ->
    {ok, dep_graph(), [file:filename()], #{file:filename() => hashes()}} | stale.
load_depgraph(Path, Key) ->
    case file:consult(Path) of
        {ok, [{etylizer_depgraph, ?DEPGRAPH_VERSION, Key, Saved, DepGraph}]} ->
            Old = ?assert_type(Saved, [{file:filename(), hashes()}]),
            New = [{F, hashes([H || {H, _} <- Hs])} || {F, Hs} <- Old],
            case [F || {F, [{_, {error, _}} | _]} <- New] of
                [] ->
                    Kept = maps:from_list([E || {E, E} <- lists:zip(Old, New)]),
                    Changed = [F || {F, _} <- New, not maps:is_key(F, Kept)],
                    {ok, ?assert_type(DepGraph, dep_graph()), Changed, Kept};
                _ -> stale
            end;
        _ -> stale
    end.

-type source_hash() :: string() | {error, any()}.

% A source, followed by the headers it includes, with their hashes
-type hashes() :: [{file:filename(), source_hash()}].

-spec hashes([file:filename()]) -> hashes().
hashes(Files) -> [{F, utils:hash_file(F)} || F <- Files].

-spec parse_intern(file:filename()) -> [ast:form()].
parse_intern(P) -> parse_cache:parse(intern, P).
