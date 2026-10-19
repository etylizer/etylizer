-module(cm_check).

% @doc This module is responsible for orchestrating the execution of the type checks and
% updating the index. A changed file is rechecked function by function.

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

% The functions to check in a file
-type fun_filter() :: all | [ast:fun_with_arity()].
-type check_list() :: [{file:filename(), fun_filter()}].

-spec perform_type_checks(
    paths:search_path(),
    [file:filename()],
    cm_depgraph:dep_graph(),
    cmd_opts()) -> check_list().
perform_type_checks(SearchPath, SourceList, DepGraph, Opts) ->
    {CheckList, Index} = check_list(SourceList, DepGraph, Opts),
    OverlaySymtab = overlay_symtab(Opts),
    Symtab = symtab:std_symtab(SearchPath, OverlaySymtab, Opts#opts.gradual_typing_mode),
    {Checked, NewIndex} = lists:foldl(
        fun({File, Filter}, {Acc, AccIndex}) ->
            {Entry, NextIndex} =
                check_single_file(File, Filter, Symtab, OverlaySymtab, SearchPath, Opts, AccIndex),
            {[Entry | Acc], NextIndex}
        end, {[], Index}, CheckList),
    cm_index:save_index(paths:index_file_name(Opts), NewIndex),
    [E || E = {_, Funs} <- lists:reverse(Checked), Funs =/= []].

% The files to check, and the index they were determined with. An empty filter is for
% a file whose text changed, but none of its functions.
-spec check_list([file:filename()], cm_depgraph:dep_graph(), cmd_opts()) ->
    {check_list(), cm_index:index()}.
check_list(SourceList, DepGraph, Opts) ->
    RebarLockFile = paths:rebar_lock_file(Opts),
    Stamp = stamp(Opts),
    Index0 = cm_index:load_index(RebarLockFile, Stamp, paths:index_file_name(Opts)),
    {DepsChanged, Index} = cm_index:has_external_dep_changed(RebarLockFile, Stamp, Index0),
    CheckList =
        case DepsChanged orelse Opts#opts.force of
            true ->
                ?LOG_DEBUG("Rechecking everything (dependencies changed: ~p, forced: ~p)", DepsChanged, Opts#opts.force),
                [{F, all} || F <- SourceList];
            false ->
                Entries = lists:flatmap(
                    fun(Path) -> check_entries(Path, Index, DepGraph) end,
                    SourceList),
                [{F, whole_file_if_inferring(Filter, Opts)}
                 || {F, Filter} <- merge_check_entries(Entries), lists:member(F, SourceList)]
        end,
    ?LOG_DEBUG("Need to check ~p of ~p files: ~p", length(CheckList), length(SourceList), CheckList),
    {CheckList, Index}.

% what the index depend on besides the sources
-spec stamp(cmd_opts()) -> term().
stamp(Opts) ->
    Assertions = case Opts#opts.assertions of
                     undefined -> none;
                     File -> utils:hash_file(File)
                 end,
    {symtab_cache:stamp(Opts), Opts#opts.exhaustiveness_mode, Opts#opts.check_exports,
     Opts#opts.no_type_checking, lists:sort(Opts#opts.no_exhaustiveness),
     lists:sort(Opts#opts.no_redundancy), Assertions}.

-spec only_and_ignore(cmd_opts()) -> {sets:set(string()), sets:set(string())}.
only_and_ignore(Opts) ->
    {sets:from_list(Opts#opts.type_check_only), sets:from_list(Opts#opts.type_check_ignore)}.

% Inferred types depend on function bodies, so a function cannot be checked on its own.
-spec whole_file_if_inferring(fun_filter(), cmd_opts()) -> fun_filter().
whole_file_if_inferring([_ | _], #opts{gradual_typing_mode = infer}) -> all;
whole_file_if_inferring(Filter, _) -> Filter.

% What has to be checked because of the given file. A function that failed is checked
% again.
-spec check_entries(file:filename(), cm_index:index(), cm_depgraph:dep_graph()) -> check_list().
check_entries(Path, Index, DepGraph) ->
    Recheck = cm_index:needs_recheck(Path, Index),
    case Recheck =:= [] andalso not cm_index:has_file_changed(Path, Index) of
        true -> [];
        false ->
            Forms = parse_cache:parse(intern, Path),
            {Changed, Affecting} = cm_index:changed_functions(Path, Forms, Index),
            % The files using the module only depend on its exported interface
            Deps = case Changed =:= all
                        andalso cm_index:has_exported_interface_changed(Path, Forms, Index) of
                true -> cm_depgraph:find_dependent_files(Path, DepGraph);
                false -> []
            end,
            % A function with a new spec, or one that is gone, affects its callers
            Mod = ast_utils:modname_from_path(Path),
            Callers = cm_index:callers([{Mod, N, A} || {N, A} <- Affecting], Index),
            ?LOG_DEBUG("Need to check ~200p in ~p, the files using its interface: ~200p, "
                "and the callers of new specs: ~200p", Changed, Path, Deps, Callers),
            [{Path, merge_filters(Changed, Recheck)} | [{D, all} || D <- Deps] ++ Callers]
    end.

% One entry per file
-spec merge_check_entries(check_list()) -> check_list().
merge_check_entries(Entries) ->
    maps:to_list(lists:foldl(
        fun({File, Funs}, Acc) ->
            maps:put(File, merge_filters(Funs, maps:get(File, Acc, [])), Acc)
        end, #{}, Entries)).

-spec merge_filters(fun_filter(), fun_filter()) -> fun_filter().
merge_filters(all, _) -> all;
merge_filters(_, all) -> all;
merge_filters(Funs1, Funs2) -> lists:usort(Funs1 ++ Funs2).

% Checks the functions of the filter that the command line selects and records the
% result. Returns what was checked.
-spec check_single_file(
    file:filename(), fun_filter(), symtab:t(), symtab:t(),
    paths:search_path(), cmd_opts(), cm_index:index())
    -> {{file:filename(), fun_filter()}, cm_index:index()}.
check_single_file(CurrentFile, Filter, Symtab, OverlaySymtab, SearchPath, Opts, Index) ->
    Forms = parse_cache:parse(intern, CurrentFile),
    Checked = selection(CurrentFile, Forms, Filter, Opts),
    Failed =
        case Checked of
            [] ->
                ?LOG_DEBUG("Nothing to check in ~s (filter: ~200p)", CurrentFile, Filter),
                [];
            _ ->
                ?LOG_DEBUG("Checking ~s (filter: ~200p)", CurrentFile, Checked),
                ModName = ast_utils:modname_from_path(CurrentFile),
                Referenced = [M || M <- ast_utils:referenced_modules(Forms), M =/= ModName],
                ?LOG_DEBUG("Referenced from ~s: ~200p", CurrentFile, Referenced),
                ExpandedSymtab = symtab:extend_symtab_with_module_list(Symtab, SearchPath, Referenced, OverlaySymtab),
                {Only, Ignore} =
                    case Checked of
                        all -> only_and_ignore(Opts);
                        _ ->
                            QRefs = [utils:sformat("~w:~w/~w", ModName, N, A) || {N, A} <- Checked],
                            {sets:from_list(QRefs), sets:new()}
                    end,
                do_type_check(CurrentFile, Forms, Only, Ignore, ExpandedSymtab, OverlaySymtab, Opts)
        end,
    Headers = parse_cache:headers(CurrentFile),
    {{CurrentFile, Checked}, cm_index:insert(CurrentFile, Forms, Headers, Failed, Index)}.

% The functions of the filter that the command line selects
-spec selection(file:filename(), ast:forms(), fun_filter(), cmd_opts()) -> fun_filter().
selection(_, _, all, _) -> all;
selection(File, Forms, Filter, Opts) ->
    {Only, Ignore} = only_and_ignore(Opts),
    ModName = ast_utils:modname_from_path(File),
    Funs = [{N, A} || {function, _, N, A, _, _} <- Forms],
    [F || F <- Filter, lists:member(F, Funs), typing:should_check(ModName, F, Only, Ignore)].

% Returns the functions that failed (empty in early-exit mode).
-spec do_type_check(
    file:filename(), ast:forms(), sets:set(string()), sets:set(string()),
    symtab:t(), symtab:t(), cmd_opts()
) -> [{ast:fun_with_arity(), cm_index:failure()}].
do_type_check(CurrentFile, Forms, Only, Ignore, ExpandedSymtab, OverlaySymtab, Opts) ->
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
            typing:check_forms(Ctx, CurrentFile, Forms, Only, Ignore,
                Opts#opts.check_exports, {CliNoExhaustiveness, CliNoRedundancy})
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
    lists:foldl(
        fun(OverlayFile, Tab) ->
            ?LOG_INFO("Using overlays from ~s", OverlayFile),
            symtab:overlay_symtab(parse_cache:parse(intern, OverlayFile), Tab)
        end,
        symtab:empty(),
        Opts#opts.type_overlay).
