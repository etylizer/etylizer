-module(paths).

% @doc This module contains functionality related to handling file system paths.

-export([compute_search_path/1, generate_input_file_list/1, index_file_name/1, find_module_path/2]).
-export_type([search_path_entry/0, search_path/0]).

-include_lib("log.hrl").
-include_lib("ety_main.hrl").

% An entry in the search path is a kind (local, dep, or otp), a source directory and a list
% of include directories.
% Parsing a file in the directory requires the include path to be set according to the
% include directories.
-type search_path_entry() :: {local | dep | otp, file:filename(), [file:filename()]}.

-type search_path() :: [search_path_entry()].

-spec root_dir(cmd_opts()) -> file:filename().
root_dir(Opts) ->
    case Opts#opts.project_root of
        empty -> ".";
        D -> D
    end.

-spec compute_search_path(cmd_opts()) -> search_path().
compute_search_path(Opts) ->
    RootDir = root_dir(Opts),
    ImplicitDirs = lists:map(fun(F) -> filename:dirname(F) end, Opts#opts.files),
    {LocalPathEntries, _} =
        lists:foldl(
            fun(P, {Acc, Set}) ->
                NormP = filename:nativename(P),
                case sets:is_element(NormP, Set) of
                    true -> {Acc, Set};
                    false -> {[{local, NormP, Opts#opts.includes} | Acc],
                                sets:add_element(NormP, Set)}
                end
            end,
            {[], sets:new()},
            ImplicitDirs ++ Opts#opts.src_paths),
    lists:reverse(LocalPathEntries) ++ find_dependency_roots(RootDir) ++ find_otp_paths().

-spec standard_path_entry(
    dep | otp, file:filename(), file:filename(), [file:filename()]) -> search_path_entry().
standard_path_entry(Kind, D1, D2, ExtraIncludes) ->
    D = filename:join(D1, D2),
    SrcDir = filename:join(D, "src"),
    {Kind, SrcDir, [SrcDir, filename:join(D, "include")] ++ ExtraIncludes}.

-spec find_otp_paths() -> search_path().
find_otp_paths() ->
    RootDir = code:lib_dir(),
    StdlibIncludeDir = filename:join(code:lib_dir(stdlib), "include"),
    {ok, Dirs} = file:list_dir(RootDir),
    lists:map(fun(Path) -> standard_path_entry(otp, RootDir, Path, [StdlibIncludeDir]) end, Dirs).

-spec find_dependency_roots(file:filename()) -> search_path().
find_dependency_roots(ProjectDir) ->
    ProjectBuildDir = filename:join([ProjectDir, "_build"]),
    ProjectLibDir = filename:join([ProjectBuildDir, "default/lib"]),
    case filelib:is_dir(ProjectBuildDir) of
        true ->
            {ok, PathList} = file:list_dir(ProjectLibDir),
            lists:map(fun(Path) -> standard_path_entry(dep, ProjectLibDir, Path, []) end, PathList);
        false ->
            ?ABORT("_build/ directory not found. The project needs to be build at least once before etylizer can run.")
    end.

-spec generate_input_file_list(cmd_opts()) -> [file:filename()].
generate_input_file_list(Opts) ->
    case Opts#opts.src_paths of
        [] ->
            case Opts#opts.files of
                [] -> utils:quit(1, "No input files given, aborting");
                Files -> Files
            end;
        Paths ->
            lists:foldl(fun(Path, FileList) -> FileList ++ add_dir_to_list(Path) end, [], Paths)
    end.

-spec add_dir_to_list(file:filename()) -> [file:filename()].
add_dir_to_list(Path) ->
    case file:list_dir(Path) of
        {ok, []} ->
            []; % Exit recursion if directory is empty
        {ok, DirContent} ->
            {Dirs, Files} = lists:splitwith(fun(F) -> filelib:is_dir(F) end, DirContent),
            Sources = lists:filter(
                        fun(F) ->
                                case string:find(F, ".erl") of
                                    nomatch -> false;
                                    _ -> true
                                end
                        end, Files),
            SourcesFull = lists:map(fun(F) -> filename:join(Path, F) end, Sources),
            ChildSources = lists:append(lists:map(fun(F) -> add_dir_to_list(filename:join(Path, F)) end, Dirs)),
            lists:append(SourcesFull, ChildSources);
        {error, Reason} ->
            ?ABORT("Error occurred while scanning for erlang sources. Reason: ~s", Reason)
    end.

-spec etylizer_dir(cmd_opts()) -> file:filename().
etylizer_dir(Opts) ->
    RootDir = root_dir(Opts),
    filename:join(RootDir, "_etylizer").

-spec index_file_name(cmd_opts()) -> file:filename().
index_file_name(Opts) ->
    D = etylizer_dir(Opts),
    filename:join(D, "index").

-spec find_module_path(paths:search_path(), atom()) -> paths:search_path_entry().
find_module_path(SearchPath, Module) ->
    Filename = string:concat(atom_to_list(Module), ".erl"),
    SearchResult = lists:search(
      fun({_, SrcPath, _Includes}) ->
            case filelib:find_file(Filename, SrcPath) of
                {ok, _} -> true;
                {error, not_found} -> false
            end
      end, SearchPath),
    case SearchResult of
        {value, {Kind, SrcPath, Includes}} ->
            File = filename:join(SrcPath, Filename),
            ?LOG_DEBUG("Resolved module ~p to file ~p", Module, File),
            {Kind, File, Includes};
        false ->
            Dirs = lists:map(fun({_, P, _}) -> P end, SearchPath),
            ?ABORT("Module ~p not found, search path: ~p", Module, Dirs)
    end.
