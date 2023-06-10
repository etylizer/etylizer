-module(paths).

% @doc This module contains functionality related to handling file system paths.

-export([find_search_paths/1, generate_file_list/1]).

-include_lib("log.hrl").
-include_lib("ety_main.hrl").

-spec find_search_paths(cmd_opts()) -> [file:filename()].
find_search_paths(Opts) ->
    Opts#opts.src_paths ++ find_dependency_roots(Opts#opts.project_root) ++ find_otp_paths().

-spec find_otp_paths() -> [file:filename()].
find_otp_paths() ->
    RootDir = code:lib_dir(),
    {ok, Files} = file:list_dir(RootDir),
    lists:map(fun(Path) -> filename:join([RootDir, Path]) end, Files).

-spec find_dependency_roots(file:filename()) -> [file:filename()].
find_dependency_roots(ProjectDir) ->
    ProjectBuildDir = filename:join([ProjectDir, "_build"]),
    ProjectLibDir = filename:join([ProjectBuildDir, "default/lib"]),

    case filelib:is_dir(ProjectBuildDir) of
        true ->
            {ok, PathList} = file:list_dir(ProjectLibDir),
            lists:map(fun(Path) -> filename:join([ProjectLibDir, Path]) end, PathList);
        false ->
            ?ABORT("_build/ directory not found. The project needs to be build at least once before etylizer can run.")
    end.

-spec generate_file_list(cmd_opts()) -> [file:filename()].
generate_file_list(Opts) ->
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
