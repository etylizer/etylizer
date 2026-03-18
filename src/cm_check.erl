-module(cm_check).

% @doc This module is responsible for orchestrating the execution of the type checks and
% updating the index. Supports function-level incremental type checking.

-export([
    perform_type_checks/4
]).

-export_type([check_list/0]).

-ifdef(TEST).
-export([perform_sanity_check/3, perform_sanity_check/4]).
-endif.

-include("log.hrl").
-include("etylizer_main.hrl").
-include("parse.hrl").
-include("etylizer.hrl").

-type check_entry() :: {file:filename(), all | [{atom(), arity()}]}.
-type check_list() :: [check_entry()].

-spec perform_type_checks(
    paths:search_path(),
    [file:filename()],
    cm_depgraph:dep_graph(),
    cmd_opts()) -> check_list().
perform_type_checks(SearchPath, SourceList, DepGraph, Opts) ->
    IndexFile = paths:index_file_name(Opts),
    RebarLockFile = paths:rebar_lock_file(Opts),
    Index = cm_index:load_index(RebarLockFile, IndexFile, Opts#opts.mode),
    {DepsChanged, NewIndex0} =
        cm_index:has_external_dep_changed(RebarLockFile, Index),
    NewIndex1 = case Opts#opts.no_deps of
        true -> NewIndex0;
        false -> cm_index:prune(NewIndex0, SourceList)
    end,
    CheckList = compute_check_list(SourceList, NewIndex1, DepGraph, DepsChanged, Opts),
    rebuild_dep_graphs_if_needed(CheckList, SearchPath, DepGraph, Opts),
    _ = rebuild_fun_dep_graph(SourceList, CheckList, paths:fun_depgraph_file_name(Opts)),
    run_checks_and_save(CheckList, SearchPath, Opts, NewIndex1, IndexFile).

% @doc Run type checks and save the index.
-spec run_checks_and_save(
    check_list(), paths:search_path(), cmd_opts(), cm_index:index(), file:filename()
) -> check_list().
run_checks_and_save(CheckList, SearchPath, Opts, Index, IndexFile) ->
    OverlaySymtab = overlay_symtab(Opts),
    Symtab = symtab:std_symtab(SearchPath, OverlaySymtab),
    NewIndex = traverse_and_check(CheckList, Symtab,
        OverlaySymtab, SearchPath, Opts, Index),
    cm_index:save_index(IndexFile, NewIndex),
    CheckList.

% @doc Determine which check list to use based on deps/force status.
-spec compute_check_list(
    [file:filename()], cm_index:index(), cm_depgraph:dep_graph(), boolean(), cmd_opts()
) -> check_list().
compute_check_list(SourceList, Index, DepGraph, DepsChanged, Opts) ->
    FunDepGraphFile = paths:fun_depgraph_file_name(Opts),
    FunDepGraph = case cm_depgraph:load_fun_depgraph(FunDepGraphFile) of
        {ok, G} -> G;
        stale -> ?assert_type(maps:new(), cm_depgraph:fun_dep_graph())
    end,
    CheckList =
        case {DepsChanged, Opts#opts.force} of
            {false, false} ->
                ?LOG_TRACE("No external dependency has changed"),
                create_check_list(SourceList, Index, DepGraph, FunDepGraph);
            {true, _} ->
                ?LOG_DEBUG("Some external dependency has changed, rechecking everything"),
                [{F, all} || F <- SourceList];
            {_, true} ->
                ?LOG_TRACE("Forced to recheck everything"),
                [{F, all} || F <- SourceList]
        end,
    log_check_list(CheckList, SourceList),
    CheckList.

% @doc Log check list summary.
-spec log_check_list(check_list(), [file:filename()]) -> ok.
log_check_list([], SourceList) ->
    ?LOG_DEBUG("Need to check 0 of ~p files", length(SourceList)), ok;
log_check_list(CheckList, SourceList) ->
    ?LOG_DEBUG("Need to check ~p of ~p files: ~p",
        length(CheckList), length(SourceList), CheckList), ok.

% @doc Incrementally update and save the module-level dep graph for changed files.
-spec rebuild_dep_graphs_if_needed(
    check_list(), paths:search_path(), cm_depgraph:dep_graph(), cmd_opts()
) -> ok.
rebuild_dep_graphs_if_needed(CheckList, SearchPath, DepGraph, Opts) ->
    ChangedFiles = [F || {F, _} <- CheckList],
    DepGraphFile = paths:depgraph_file_name(Opts),
    case ChangedFiles =/= [] andalso not Opts#opts.no_deps of
        true ->
            ?LOG_DEBUG("Incrementally updating dependency graph (~p changed files)",
                length(ChangedFiles)),
            % Remove old edges for changed files, then re-add from current AST
            Pruned = lists:foldl(
                fun(F, G) -> cm_depgraph:remove_dependent(F, G) end,
                DepGraph, ChangedFiles),
            Updated = lists:foldl(
                fun(F, G) ->
                    Forms = parse_cache:parse(intern, F),
                    cm_depgraph:update_dep_graph(F, Forms, SearchPath, G)
                end,
                Pruned, ChangedFiles),
            cm_depgraph:save_depgraph(DepGraphFile, Updated);
        false -> ok
    end.

% @doc Rebuild function dep graph, incrementally if possible.
-spec rebuild_fun_dep_graph([file:filename()], check_list(), file:filename()) -> cm_depgraph:fun_dep_graph().
rebuild_fun_dep_graph(SourceList, CheckList, FunDepGraphFile) ->
    ChangedFiles = [F || {F, _} <- CheckList],
    case ChangedFiles of
        [] ->
            % Nothing changed, reuse existing graph
            case cm_depgraph:load_fun_depgraph(FunDepGraphFile) of
                {ok, G} -> G;
                stale -> ?assert_type(maps:new(), cm_depgraph:fun_dep_graph())
            end;
        _ ->
            case cm_depgraph:load_fun_depgraph(FunDepGraphFile) of
                {ok, OldGraph} ->
                    % Incremental: only re-analyze changed files
                    ?LOG_DEBUG("Incrementally updating function dependency graph (~p changed files)",
                        length(ChangedFiles)),
                    ChangedMods = sets:from_list(
                        [ast_utils:modname_from_path(F) || F <- ChangedFiles],
                        [{version, 2}]),
                    ChangedModInfos = analyze_files(ChangedFiles),
                    Graph = cm_depgraph:update_fun_dep_graph(
                        OldGraph, ChangedMods, ChangedModInfos),
                    cm_depgraph:save_fun_depgraph(FunDepGraphFile, Graph),
                    Graph;
                stale ->
                    % No existing graph, full rebuild from all files
                    ?LOG_DEBUG("Building function dependency graph from scratch"),
                    ModInfos = analyze_files(SourceList),
                    Graph = cm_depgraph:build_fun_dep_graph(ModInfos),
                    cm_depgraph:save_fun_depgraph(FunDepGraphFile, Graph),
                    Graph
            end
    end.

% @doc Parse and analyze a list of source files.
-spec analyze_files([file:filename()]) -> [{file:filename(), cm_fun_deps:module_info()}].
analyze_files(Files) ->
    lists:map(
        fun(Path) ->
            Forms = parse_cache:parse(intern, Path),
            ModName = ast_utils:modname_from_path(Path),
            {Path, cm_fun_deps:analyze_module(ModName, Forms)}
        end, Files).

-spec create_check_list(
    [file:filename()], cm_index:index(), cm_depgraph:dep_graph(), cm_depgraph:fun_dep_graph()
) -> check_list().
create_check_list(SourceList, Index, DepGraph, FunDepGraph) ->
    ModToPath = maps:from_list(
        [{ast_utils:modname_from_path(P), P} || P <- SourceList]),
    CheckEntries = lists:foldl(
        fun(Path, Acc) ->
            process_source_file(Path, Index, DepGraph, FunDepGraph, ModToPath, Acc)
        end, [], SourceList),
    merge_check_entries(CheckEntries).

% @doc Process a single source file and determine what needs rechecking.
-spec process_source_file(
    file:filename(), cm_index:index(), cm_depgraph:dep_graph(),
    cm_depgraph:fun_dep_graph(), #{atom() => file:filename()}, check_list()
) -> check_list().
process_source_file(Path, Index, DepGraph, FunDepGraph, ModToPath, Acc) ->
    case cm_index:has_file_changed(Path, Index) of
        false -> Acc;
        true ->
            ?LOG_DEBUG("Need to check ~p because the file has changed.", Path),
            Forms = parse_cache:parse(intern, Path),
            ModName = ast_utils:modname_from_path(Path),
            ModInfo = cm_fun_deps:analyze_module(ModName, Forms),
            {ChangedFuns, DeclsChanged} = cm_index:changed_functions(Path, ModInfo, Index),
            process_changed_file(Path, Forms, ModName, ModInfo, ChangedFuns,
                DeclsChanged, Index, DepGraph, FunDepGraph, ModToPath, Acc)
    end.

% @doc Handle a file that has changed, determining check entries.
-spec process_changed_file(
    file:filename(), ast:forms(), atom(), cm_fun_deps:module_info(),
    all | [ast:fun_with_arity()], boolean(),
    cm_index:index(), cm_depgraph:dep_graph(), cm_depgraph:fun_dep_graph(),
    #{atom() => file:filename()}, check_list()
) -> check_list().
process_changed_file(Path, Forms, _ModName, _ModInfo, _ChangedFuns,
        true, Index, DepGraph, _FunDepGraph, _ModToPath, Acc) ->
    % Types/records/exports changed: recheck all in this file.
    % Only recheck dependents if the exported interface actually changed
    % (e.g. a local type change doesn't affect dependents).
    Deps = case cm_index:has_exported_interface_changed(Path, Forms, Index) of
        true ->
            FoundDeps = cm_depgraph:find_dependent_files(Path, DepGraph),
            case FoundDeps of
                [] -> ok;
                _ ->
                    ?LOG_DEBUG("Need to check the following files because the " ++
                        "interface of ~p has changed: ~200p", Path, FoundDeps)
            end,
            [{D, all} || D <- FoundDeps];
        false -> []
    end,
    Acc ++ [{Path, all}] ++ Deps;
process_changed_file(Path, _Forms, ModName, ModInfo, ChangedFuns,
        false, Index, _DepGraph, FunDepGraph, ModToPath, Acc) ->
    case ChangedFuns of
        all ->
            % All functions changed but decls didn't. Find callers of spec-changed funs.
            AllFunIds = [FId || FId <- maps:keys(
                ?assert_type(maps:get(funs, ModInfo), #{cm_fun_deps:fun_id() => cm_fun_deps:fun_info()}))],
            SpecChangedFunIds = find_all_spec_changed_funs(AllFunIds, ModInfo, Path, Index),
            {LocalCallers, CrossEntries} = find_affected_callers(
                SpecChangedFunIds, FunDepGraph, ModName, ModToPath),
            Acc ++ [{Path, all}] ++ [{Path, LocalCallers} || LocalCallers =/= []] ++ CrossEntries;
        [] ->
            % No functions changed (only whitespace/comments?)
            Acc ++ [{Path, []}];
        Funs ->
            SpecChangedFuns = find_spec_changed_funs(ModName, Funs, ModInfo, Path, Index),
            {LocalCallers, CrossEntries} = find_affected_callers(
                SpecChangedFuns, FunDepGraph, ModName, ModToPath),
            AllLocalFuns = lists:uniq(Funs ++ LocalCallers),
            Acc ++ [{Path, AllLocalFuns}] ++ CrossEntries
    end.

% @doc Find functions whose specs changed from the set of changed functions.
-spec find_spec_changed_funs(
    atom(), [ast:fun_with_arity()], cm_fun_deps:module_info(),
    file:filename(), cm_index:index()
) -> [cm_fun_deps:fun_id()].
find_spec_changed_funs(ModName, ChangedFuns, ModInfo, Path, {_, IndexMap}) ->
    lists:filtermap(
        fun(FA) ->
            check_spec_changed(ModName, FA, ModInfo, Path, IndexMap)
        end, ChangedFuns).

% @doc Check all fun_ids for spec changes (used when ChangedFuns = all).
-spec find_all_spec_changed_funs(
    [cm_fun_deps:fun_id()], cm_fun_deps:module_info(),
    file:filename(), cm_index:index()
) -> [cm_fun_deps:fun_id()].
find_all_spec_changed_funs(FunIds, ModInfo, Path, {_, IndexMap}) ->
    lists:filtermap(
        fun({ModName, Name, Arity}) ->
            check_spec_changed(ModName, {Name, Arity}, ModInfo, Path, IndexMap)
        end, FunIds).

% @doc Check if a single function's spec has changed.
-spec check_spec_changed(
    atom(), ast:fun_with_arity(), cm_fun_deps:module_info(),
    file:filename(), #{file:filename() => cm_index:file_index_entry()}
) -> {true, cm_fun_deps:fun_id()} | false.
check_spec_changed(ModName, {Name, Arity}, ModInfo, Path, IndexMap) ->
    FunId = {ModName, Name, Arity},
    Funs = ?assert_type(maps:get(funs, ModInfo), #{cm_fun_deps:fun_id() => cm_fun_deps:fun_info()}),
    case maps:find(FunId, Funs) of
        error -> false;
        {ok, FunInfo} ->
            NewSpecHash = ?assert_type(maps:get(spec_hash, FunInfo), string()),
            case maps:find(Path, IndexMap) of
                error ->
                    % File not in index, treat spec as changed
                    {true, FunId};
                {ok, {_, _, _, OldFunIndex}} ->
                    case maps:find({Name, Arity}, OldFunIndex) of
                        error ->
                            % New function, treat spec as changed
                            {true, FunId};
                        {ok, {failed, OldSpecHash}} ->
                            % Previously failed - compare spec hashes
                            case NewSpecHash =/= OldSpecHash of
                                true -> {true, FunId};
                                false -> false
                            end;
                        {ok, {_OldBodyHash, OldSpecHash}} ->
                            case NewSpecHash =/= OldSpecHash of
                                true -> {true, FunId};
                                false -> false
                            end
                    end
            end
    end.

% @doc Find callers of spec-changed functions, both same-module and cross-module.
% Returns {LocalCallers, CrossFileEntries} where LocalCallers are {Name, Arity}
% pairs in the same module, and CrossFileEntries are check_list entries for other files.
-spec find_affected_callers(
    [cm_fun_deps:fun_id()], cm_depgraph:fun_dep_graph(),
    atom(), #{atom() => file:filename()}
) -> {[ast:fun_with_arity()], check_list()}.
find_affected_callers([], _FunDepGraph, _SourceMod, _ModToPath) ->
    {[], []};
find_affected_callers(SpecChangedFuns, FunDepGraph, SourceMod, ModToPath) ->
    AllCallers = lists:flatmap(
        fun(FunId) -> cm_depgraph:find_fun_callers(FunId, FunDepGraph) end,
        SpecChangedFuns),
    % Separate same-module callers from cross-module callers
    {SameModCallers, CrossModCallers} = lists:partition(
        fun({Mod, _, _}) -> Mod =:= SourceMod end, AllCallers),
    LocalFuns = lists:uniq([{Name, Arity} || {_, Name, Arity} <- SameModCallers]),
    % Group cross-module callers by module, then map to file paths
    CallersByMod = lists:foldl(
        fun({Mod, FName, FArity}, Acc) ->
            Existing = maps:get(Mod, Acc, []),
            maps:put(Mod, [{FName, FArity} | Existing], Acc)
        end, ?assert_type(maps:new(), #{atom() => [ast:fun_with_arity()]}), CrossModCallers),
    CrossEntries = lists:filtermap(
        fun({Mod, FunsInMod}) ->
            case maps:find(Mod, ModToPath) of
                {ok, FilePath} ->
                    UniqFuns = lists:uniq(?assert_type(FunsInMod, [ast:fun_with_arity()])),
                    ?LOG_INFO("Need to recheck ~200p in ~p because called specs changed",
                        UniqFuns, FilePath),
                    {true, {FilePath, UniqFuns}};
                error ->
                    % Module not in our source list (external dep)
                    false
            end
        end, maps:to_list(CallersByMod)),
    {LocalFuns, CrossEntries}.

% @doc Merge check entries, combining per-file function lists and deduplicating.
-spec merge_check_entries(check_list()) -> check_list().
merge_check_entries(Entries) ->
    Merged = lists:foldl(
        fun(Entry, Acc) -> merge_single_entry(Entry, Acc) end,
        ?assert_type(maps:new(), #{file:filename() => all | [{atom(), arity()}]}),
        Entries),
    [{F, Fs} || {F, Fs} <- maps:to_list(Merged), Fs =:= all orelse Fs =/= []].

% @doc Merge a single check entry into the accumulator map.
-spec merge_single_entry(
    check_entry(), #{file:filename() => all | [{atom(), arity()}]}
) -> #{file:filename() => all | [{atom(), arity()}]}.
merge_single_entry({File, Funs}, Acc) ->
    case maps:find(File, Acc) of
        error ->
            maps:put(File, Funs, Acc);
        {ok, all} ->
            Acc;
        {ok, _ExistingFuns} when Funs =:= all ->
            maps:put(File, all, Acc);
        {ok, ExistingFuns} ->
            maps:put(File, lists:uniq(?assert_type(ExistingFuns, [{atom(), arity()}]) ++ ?assert_type(Funs, [{atom(), arity()}])), Acc)
    end.

-spec traverse_and_check(
    check_list(), symtab:t(), symtab:t(), paths:search_path(), cmd_opts(), cm_index:index())
    -> cm_index:index().
traverse_and_check([], _, _, _, _, Index) ->
    Index;
traverse_and_check([{CurrentFile, FunFilter} | Remaining], Symtab, OverlaySymtab, SearchPath, Opts, Index) ->
    NewIndex = check_single_file(CurrentFile, FunFilter, Symtab, OverlaySymtab, SearchPath, Opts, Index),
    traverse_and_check(Remaining, Symtab, OverlaySymtab, SearchPath, Opts, NewIndex).

-spec check_single_file(
    file:filename(), all | [{atom(), arity()}], symtab:t(), symtab:t(),
    paths:search_path(), cmd_opts(), cm_index:index())
    -> cm_index:index().
check_single_file(CurrentFile, FunFilter, Symtab, OverlaySymtab, SearchPath, Opts, Index) ->
    ModName = ast_utils:modname_from_path(CurrentFile),
    Only = build_only_set(FunFilter, Opts#opts.type_check_only, ModName),
    case {sets:is_empty(Only), Opts#opts.type_check_only} of
        {true, [_|_]} ->
            % -o specified but no functions match for this file, skip entirely
            ?LOG_DEBUG("Skipping ~s: no functions match -o filter", CurrentFile),
            Index;
        _ ->
            ?LOG_DEBUG("Checking ~s (filter: ~200p)", CurrentFile, FunFilter),
            Forms = parse_cache:parse(intern, CurrentFile),
            Referenced = [M || M <- ast_utils:referenced_modules(Forms), M =/= ModName],
            ?LOG_DEBUG("Referenced from ~s: ~200p", CurrentFile, Referenced),
            ExpandedSymtab = symtab:extend_symtab_with_module_list(Symtab, SearchPath, Referenced, OverlaySymtab),
            FailedFuns = do_type_check(CurrentFile, Forms, Only, ExpandedSymtab, OverlaySymtab, Opts),
            cm_index:insert(CurrentFile, Forms, FailedFuns, Index)
    end.

% @doc Run type check and return the list of functions that failed (empty in early-exit mode).
-spec do_type_check(
    file:filename(), ast:forms(), sets:set(string()), symtab:t(), symtab:t(), cmd_opts()
) -> [{atom(), arity()}].
do_type_check(CurrentFile, Forms, Only, ExpandedSymtab, OverlaySymtab, Opts) ->
    Sanity = perform_sanity_check(CurrentFile, Forms, Opts#opts.sanity),
    Ctx = typing:new_ctx(ExpandedSymtab, OverlaySymtab, Sanity,
        Opts#opts.report_mode, Opts#opts.report_timeout,
        Opts#opts.exhaustiveness_mode, Opts#opts.gradual_typing_mode),
    CliNoExhaustiveness = utils:parse_fun_ids(Opts#opts.no_exhaustiveness),
    CliNoRedundancy = utils:parse_fun_ids(Opts#opts.no_redundancy),
    case Opts#opts.no_type_checking of
        true ->
            ?LOG_INFO("Not type checking ~p as requested", CurrentFile),
            [];
        false ->
            typing:check_forms(Ctx, CurrentFile, Forms,
                Only,
                sets:from_list(Opts#opts.type_check_ignore, [{version, 2}]),
                Opts#opts.check_exports,
                {CliNoExhaustiveness, CliNoRedundancy})
    end.

% @doc Build the Only set from function filter and CLI --only flag.
% Uses multi-level matching (module, module:name/arity, name/arity, name) consistent
% with typing:should_check/6.
-spec build_only_set(all | [{atom(), arity()}], [string()], atom()) -> sets:set(string()).
build_only_set(all, CliOnly, _ModName) ->
    sets:from_list(CliOnly, [{version, 2}]);
build_only_set(FunFilter, [], _ModName) when is_list(FunFilter) ->
    sets:from_list(
        [utils:sformat("~w/~w", Name, Arity) || {Name, Arity} <- FunFilter],
        [{version, 2}]);
build_only_set(FunFilter, CliOnly, ModName) when is_list(FunFilter) ->
    CliSet = sets:from_list(CliOnly, [{version, 2}]),
    ModStr = utils:sformat("~w", ModName),
    case sets:is_element(ModStr, CliSet) of
        true ->
            % Module-level match: all FunFilter functions are included
            sets:from_list(
                [utils:sformat("~w/~w", Name, Arity) || {Name, Arity} <- FunFilter],
                [{version, 2}]);
        false ->
            % Per-function matching using same levels as typing:should_check/6
            MatchingFuns = lists:filter(fun({Name, Arity}) ->
                QRefStr = utils:sformat("~w:~w/~w", ModName, Name, Arity),
                RefStr = utils:sformat("~w/~w", Name, Arity),
                NameStr = utils:sformat("~w", Name),
                sets:is_element(QRefStr, CliSet)
                orelse sets:is_element(RefStr, CliSet)
                orelse sets:is_element(NameStr, CliSet)
            end, FunFilter),
            sets:from_list(
                [utils:sformat("~w/~w", N, A) || {N, A} <- MatchingFuns],
                [{version, 2}])
    end.

-spec perform_sanity_check(file:filename(), ast:forms(), boolean()) -> {ok, ast_check:ty_map()} | error.
perform_sanity_check(CurrentFile, Forms, DoCheck) ->
    perform_sanity_check(CurrentFile, Forms, DoCheck, []).

-spec perform_sanity_check(file:filename(), ast:forms(), boolean(), [string()]) -> {ok, ast_check:ty_map()} | error.
perform_sanity_check(CurrentFile, Forms, DoCheck, Includes) ->
    if DoCheck ->
            ParseOpts = #parse_opts{includes = Includes},
            ?LOG_INFO("Checking whether transformation result for ~p conforms to AST in "
                      "ast.erl ...", CurrentFile),
            {AstSpec, _} = ast_check:parse_spec("src/ast.erl", ParseOpts),
            case ast_check:check_against_type(AstSpec, ast, forms, Forms) of
                true ->
                    ?LOG_INFO("Transform result from ~s conforms to AST in ast.erl", CurrentFile);
                false ->
                    ?ABORT("Transform result from ~s violates AST in ast.erl", CurrentFile)
            end,
            {SpecConstr, _} = ast_check:parse_spec("src/constr.erl", ParseOpts),
            SpecFullConstr = ast_check:merge_specs([SpecConstr, AstSpec]),
            {ok, SpecFullConstr};
       true -> error
    end.

-spec overlay_symtab(cmd_opts()) -> symtab:t().
overlay_symtab(Opts) ->
    OverlayForms = case Opts#opts.type_overlay of
        [] ->
            ?LOG_DEBUG("Not using any overlays"),
            [];
        OverlayFile ->
            ?LOG_INFO("Using overlays from ~s", OverlayFile),
            parse_cache:parse(intern, OverlayFile)
    end,
    symtab:overlay_symtab(OverlayForms).
