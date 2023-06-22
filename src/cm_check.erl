-module(cm_check).

% @doc This module is responsible for orchestrating the execution of the type checks and
% updating the index.

-export([perform_type_checks/4]).

-include_lib("log.hrl").
-include_lib("ety_main.hrl").

-define(INDEX_FILE_NAME, "index.json").

-spec perform_type_checks([file:filename()], symtab:t(), cmd_opts(), cm_depgraph:dependency_graph()) -> ok.
perform_type_checks(SourceList, Symtab, Opts, DependencyGraph) ->
    Index = cm_index:load_index(?INDEX_FILE_NAME),
    CheckList = create_check_list(SourceList, Index, DependencyGraph),
    NewIndex = traverse_and_check(CheckList, Symtab, Opts, Index),
    cm_index:save_index(?INDEX_FILE_NAME, NewIndex).

-spec create_check_list([file:filename()], cm_index:index(), cm_depgraph:dependency_graph()) -> [file:filename()].
create_check_list(SourceList, Index, DependencyGraph) ->
    CheckList = lists:foldl(
                  fun(Path, FilesToCheck) ->
                          case cm_index:has_file_changed(Path, Index) of
                              true -> ChangedFile = [Path];
                              false -> ChangedFile = []
                          end,

                          [{_, Forms}] = ets:lookup(forms_table, Path),
                          case cm_index:has_exported_interface_changed(Path, Forms, Index) of
                              true -> Dependencies = cm_depgraph:find_dependent_files(Path, DependencyGraph);
                              false -> Dependencies = []
                          end,

                          FilesToCheck ++ ChangedFile ++ Dependencies
                  end, [], SourceList),
    lists:uniq(CheckList).

-spec traverse_and_check([file:filename()], symtab:t(), cmd_opts(), cm_index:index()) -> cm_index:index().
traverse_and_check([], _, _, Index) ->
    Index;

traverse_and_check([CurrentFile | RemainingFiles], Symtab, Opts, Index) ->
    ?LOG_NOTE("Preparing to check ~s", CurrentFile),
    [{_, Forms}] = ets:lookup(forms_table, CurrentFile),
    ExpandedSymtab = symtab:extend_symtab_with_module_list(Symtab, Opts, ast_utils:referenced_modules(Forms)),

    ?LOG_NOTE("Typechecking ~s ...", CurrentFile),
    Only = sets:from_list(Opts#opts.only),
    Sanity = perform_sanity_check(CurrentFile, Forms, Opts),
    Ctx = typing:new_ctx(ExpandedSymtab, Sanity),
    typing:check_forms(Ctx, Forms, Only),

    NewIndex = cm_index:insert(CurrentFile, Forms, Index),
    traverse_and_check(RemainingFiles, Symtab, Opts, NewIndex).

-spec perform_sanity_check(file:filename(), ast:forms(), cmd_opts()) -> {ok, ast_check:ty_map()} | error.
perform_sanity_check(CurrentFile, Forms, Opts) ->
    if Opts#opts.sanity ->
            ?LOG_INFO("Checking whether transformation result conforms to AST in "
                      "ast.erl ..."),
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
