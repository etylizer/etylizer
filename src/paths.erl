-module(paths).

% @doc This module contains functionality related to handling file system paths.

-export([
    compute_search_path/1,
    generate_input_file_list/1,
    index_file_name/1,
    find_module_path/2,
    rebar_lock_file/1,
    rebar_config_from_lock_file/1
]).
-export_type([search_path_entry/0, search_path/0]).

-include_lib("log.hrl").
-include_lib("ety_main.hrl").

% An entry in the search path is a kind (local, dep, or otp), a source directory and a list
% of include directories.
% Parsing a file in the directory requires the include path to be set according to the
% include directories.
% NOTE (SW, 2023-06-07): the handling of include directories is very ad-hoc. Is there a better
% way of doing this?
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
    {OtpPaths, OtpIncDirs} = find_otp_paths(),
    {DepPaths, DepIncDirs} = find_dependency_roots(RootDir, OtpIncDirs),
    ImplicitDirs = lists:map(fun(F) -> filename:dirname(F) end, Opts#opts.files),
    SrcDirs = ImplicitDirs ++ Opts#opts.src_paths,
    LocalIncDirs =
        Opts#opts.includes ++
        Opts#opts.src_paths ++
        [filename:join(RootDir, "include")] ++
        DepIncDirs ++
        OtpIncDirs,
    {LocalPathEntries, _} =
        lists:foldl(
            fun(P, {Acc, Set}) ->
                NormP = filename:nativename(P),
                case sets:is_element(NormP, Set) of
                    true -> {Acc, Set};
                    false ->
                        ThisIncDir = filename:dirname(NormP),
                        {[{local, NormP, [ThisIncDir] ++ LocalIncDirs} | Acc],
                                sets:add_element(NormP, Set)}
                end
            end,
            {[], sets:new()},
            SrcDirs),
    LocalPaths = lists:reverse(LocalPathEntries),
    ?LOG_TRACE("OTP search path: ~p", OtpPaths),
    ?LOG_TRACE("rebar search path: ~p", DepPaths),
    ?LOG_TRACE("Local search path: ~p", LocalPaths),
    LocalPaths ++ DepPaths ++ OtpPaths.

-spec has_erl_files(file:filename()) -> boolean().
has_erl_files(Dir) ->
    case file:list_dir(Dir) of
        {ok, Entries} ->
            lists:any(fun(Entry) ->
                    case filename:extension(Entry) =:= ".erl" of
                        true ->
                            X = filename:join(Dir, Entry),
                            filelib:is_file(X);
                        false ->
                            false
                    end
                end, Entries);
        _ -> false
    end.

-spec find_src_dirs(file:filename()) -> [file:filename()].
find_src_dirs(SrcDir) ->
    case file:list_dir(SrcDir) of
        {error, _} -> [];
        {ok, Subs} ->
            ErlSubs = lists:filtermap(
                fun(Sub) ->
                    D = filename:join(SrcDir, Sub),
                    case filelib:is_dir(D) andalso has_erl_files(D) of
                        true -> {true, D};
                        false -> false
                    end
                end, Subs),
            case has_erl_files(SrcDir) of
                true -> [SrcDir | ErlSubs];
                false -> ErlSubs
            end
    end.

-spec standard_path_entries(
    dep | otp, file:filename(), file:filename(), [file:filename()]) -> [search_path_entry()].
standard_path_entries(Kind, D1, D2, ExtraIncludes) ->
    D = filename:join(D1, D2),
    TopSrcDir = filename:join(D, "src"),
    SrcDirs = find_src_dirs(TopSrcDir),
    Res =
        lists:map(
            fun(SrcDir) ->
                {Kind, SrcDir, [SrcDir, filename:join(D, "include")] ++ ExtraIncludes}
            end, SrcDirs),
    ?LOG_TRACE("Standard path entries for ~p: ~p", D2, Res),
    Res.

-spec find_include_dirs(file:filename(), [file:filename()]) -> [file:filename()].
find_include_dirs(RootDir, SubDirs) ->
    lists:flatmap(fun(Path) ->
        D1 = filename:join([RootDir, Path, "include"]),
        D2 = filename:join([RootDir, Path, "src"]),
        case filelib:is_dir(D1) of
            true -> [D1];
            false -> []
        end ++ case filelib:is_dir(D2) of
            true -> [D2];
            false -> []
        end
    end, SubDirs).

-spec find_otp_paths() -> {search_path(), [file:filename()]}.
find_otp_paths() ->
    RootDir = code:lib_dir(),
    {ok, Dirs} = file:list_dir(RootDir),
    IncDirs = find_include_dirs(RootDir, Dirs),
    Sp = lists:flatmap(fun(Path) -> standard_path_entries(otp, RootDir, Path, IncDirs) end, Dirs),
    {Sp, IncDirs}.

-spec find_dependency_roots(file:filename(), [file:filename()]) -> {search_path(), [file:filename()]}.
find_dependency_roots(ProjectDir, OtpIncDirs) ->
    ProjectBuildDir = filename:join([ProjectDir, "_build"]),
    ProjectLibDir = filename:join([ProjectBuildDir, "default/lib"]),
    RebarConfig = filename:join([ProjectDir, "rebar.config"]),
    case filelib:is_dir(ProjectBuildDir) of
        true ->
            case file:list_dir(ProjectLibDir) of
              {error, enoent} -> 
                {[], []};
              {ok, PathList} ->
                IncDirs = find_include_dirs(ProjectLibDir, PathList) ++ OtpIncDirs,
                Sp = lists:flatmap(fun(Path) -> standard_path_entries(dep, ProjectLibDir, Path, IncDirs) end, PathList),
                {Sp, IncDirs}
            end;
        false ->
            case filelib:is_file(RebarConfig) of
                true ->
                    ?ABORT("rebar.config found but no _build/ directory. The project needs to be build at least once before etylizer can run.");
                false ->
                    {[], []}
            end
    end.

-spec generate_input_file_list(cmd_opts()) -> [file:filename()].
generate_input_file_list(Opts) ->
    case Opts#opts.src_paths of
        [] ->
            case Opts#opts.files of
                [] -> utils:quit(1, "No input files given, aborting. Use -h to print help.~n");
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

-spec rebar_lock_file(cmd_opts()) -> file:filename().
rebar_lock_file(Opts) ->
    RootDir = root_dir(Opts),
    filename:join(RootDir, "rebar.lock").

-spec rebar_config_from_lock_file(file:filename()) -> file:filename().
rebar_config_from_lock_file(F) ->
    filename:join(filename:dirname(F), "rebar.config").

-define(TABLE, mod_table).

-spec find_module_path(paths:search_path(), atom()) -> paths:search_path_entry().
find_module_path(SearchPath, Module) ->
    case ets:whereis(?TABLE) of
        undefined -> ets:new(?TABLE, [set, named_table, {keypos, 1}]);
        _ -> ok
    end,
    Key = {SearchPath, Module},
    case ets:lookup(?TABLE, Key) of
        [{_, Result}] -> Result;
        [] ->
            X = really_find_module_path(SearchPath, Module),
            true = ets:insert(?TABLE, {Key, X}),
            X;
        Y -> ?ABORT("Unexpected entry in mod_table: ~p", Y)
    end.

-spec really_find_module_path(search_path(), atom()) -> search_path_entry().
really_find_module_path(SearchPath, Module) ->
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
