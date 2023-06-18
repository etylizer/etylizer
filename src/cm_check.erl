-module(cm_check).

% @doc This module is responsible for orchestrating the execution of the type checks and
% updating the index.

-export([perform_type_checks/4]).

-include_lib("log.hrl").
-include_lib("ety_main.hrl").

-define(INDEX_FILE_NAME, "index.json").

-spec perform_type_checks(map(), symtab:t(), cmd_opts(), map()) -> ok.
perform_type_checks(FormsList, Symtab, Opts, DependencyGraph) ->
    Index = cm_index:load_index(?INDEX_FILE_NAME),
    CheckList = create_check_list(FormsList, Index, DependencyGraph),
    NewIndex = traverse_and_check(CheckList, FormsList, Symtab, Opts, Index),
    cm_index:save_index(?INDEX_FILE_NAME, NewIndex).

-spec create_check_list(map(), map(), map()) -> [file:filename()].
create_check_list(FormsList, Index, DependencyGraph) ->
    CheckList = maps:fold(
                  fun(Path, {Forms, _}, FilesToCheck) ->
                          case cm_index:has_file_changed(Path, Index) of
                              true -> ChangedFile = [Path];
                              false -> ChangedFile = []
                          end,

                          case cm_index:has_exported_interface_changed(Path, Forms, Index) of
                              true -> Dependencies = cm_depgraph:find_dependent_files(Path, DependencyGraph);
                              false -> Dependencies = []
                          end,

                          FilesToCheck ++ ChangedFile ++ Dependencies
                  end, [], FormsList),
    lists:uniq(CheckList).

-spec traverse_and_check([file:filename()], map(), symtab:t(), cmd_opts(), cm_index:index()) -> cm_index:index().
traverse_and_check([], _, _, _, Index) ->
    Index;

traverse_and_check([CurrentFile | RemainingFiles], FormsList, Symtab, Opts, Index) ->
    ?LOG_NOTE("Preparing to check ~s", CurrentFile),
    {ok, {Forms, Sanity}} = maps:find(CurrentFile, FormsList),
    ExpandedSymtab = symtab:extend_symtab_with_module_list(Symtab, Opts, ast_utils:referenced_modules(Forms)),

    ?LOG_NOTE("Typechecking ~s ...", CurrentFile),
    Only = sets:from_list(Opts#opts.only),
    Ctx = typing:new_ctx(ExpandedSymtab, Sanity),
    typing:check_forms(Ctx, Forms, Only),

    NewIndex = cm_index:insert(CurrentFile, Forms, Index),
    traverse_and_check(RemainingFiles, FormsList, Symtab, Opts, NewIndex).
