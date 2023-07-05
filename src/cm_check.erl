-module(cm_check).

% @doc This module is responsible for orchestrating the execution of the type checks and
% updating the index.

-export([perform_type_checks/3]).

-include_lib("log.hrl").
-include_lib("ety_main.hrl").


-spec perform_type_checks(paths:search_path(), cm_depgraph:dep_graph(), cmd_opts()) -> [file:filename()].
perform_type_checks(SearchPath, DepGraph, Opts) ->
    IndexFile = paths:index_file_name(Opts),
    Index = cm_index:load_index(IndexFile, Opts#opts.mode),
    SourceList = cm_depgraph:all_sources(DepGraph),
    ?LOG_INFO("All sources: ~p", SourceList),
    CheckList = create_check_list(SourceList, Index, DepGraph),
    ?LOG_INFO("Sources to check: ~p", CheckList),
    NewIndex = traverse_and_check(CheckList, symtab:std_symtab(), SearchPath, Opts, Index),
    cm_index:save_index(IndexFile, NewIndex),
    CheckList.

-spec create_check_list([file:filename()], cm_index:index(), cm_depgraph:dep_graph()) -> [file:filename()].
create_check_list(SourceList, Index, DepGraph) ->
    CheckList = lists:foldl(
                  fun(Path, FilesToCheck) ->
                          case cm_index:has_file_changed(Path, Index) of
                              true ->
                                ?LOG_INFO("Need to check ~p because the file has changed.", Path),
                                ChangedFile = [Path];
                              false -> ChangedFile = []
                          end,
                          Forms = parse_cache:parse(intern, Path),
                          case cm_index:has_exported_interface_changed(Path, Forms, Index) of
                              true ->
                                Deps = cm_depgraph:find_dependent_files(Path, DepGraph),
                                case Deps of
                                    [] -> ok;
                                    _ ->
                                        ?LOG_INFO("Need to check the following files because the " ++
                                            "interface of ~p has changed: ~200p", Path, Deps)
                                end;
                              false -> Deps = []
                          end,
                          FilesToCheck ++ ChangedFile ++ Deps
                  end, [], SourceList),
    utils:list_uniq(CheckList).

-spec traverse_and_check(
    [file:filename()], symtab:t(), paths:search_path(), cmd_opts(), cm_index:index())
    -> cm_index:index().
traverse_and_check([], _, _, _, Index) ->
    Index;

traverse_and_check([CurrentFile | RemainingFiles], Symtab, SearchPath, Opts, Index) ->
    ?LOG_NOTE("Preparing to check ~s", CurrentFile),
    Forms = parse_cache:parse(intern, CurrentFile),
    ExpandedSymtab = symtab:extend_symtab_with_module_list(Symtab, SearchPath, ast_utils:referenced_modules(Forms)),

    ?LOG_NOTE("Typechecking ~s ...", CurrentFile),
    Only = sets:from_list(Opts#opts.type_check_only),
    Sanity = perform_sanity_check(CurrentFile, Forms, Opts),
    Ctx = typing:new_ctx(ExpandedSymtab, Sanity),
    case Opts#opts.no_type_checking of
        true ->
            ?LOG_WARN("Not type checking ~p as requested", CurrentFile);
        false ->
            typing:check_forms(Ctx, Forms, Only)
    end,
    NewIndex = cm_index:insert(CurrentFile, Forms, Index),
    traverse_and_check(RemainingFiles, Symtab, SearchPath, Opts, NewIndex).

-spec perform_sanity_check(file:filename(), ast:forms(), cmd_opts()) -> {ok, ast_check:ty_map()} | error.
perform_sanity_check(CurrentFile, Forms, Opts) ->
    if Opts#opts.sanity ->
            ?LOG_INFO("Checking whether transformation result for ~p conforms to AST in "
                      "ast.erl ...", CurrentFile),
            {AstSpec, _} = ast_check:parse_spec("src/ast.erl"),
            case ast_check:check_against_type(AstSpec, ast, forms, Forms) of
                true ->
                    ?LOG_INFO("Transform result from ~s conforms to AST in ast.erl", CurrentFile);
                false ->
                    ?ABORT("Transform result from ~s violates AST in ast.erl", CurrentFile)
            end,
            {SpecConstr, _} = ast_check:parse_spec("src/constr.erl"),
            SpecFullConstr = ast_check:merge_specs([SpecConstr, AstSpec]),
            {ok, SpecFullConstr};
       true -> error
    end.
