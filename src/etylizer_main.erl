-module(etylizer_main).
-export([
    get_espresso_binary/0,
    main/1,
    doWork/1
]).



% @doc This is the main module of etylizer. It parses commandline arguments and orchestrates
% everything.

-include("log.hrl").
-include("parse.hrl").
-include("etylizer_main.hrl").

-spec parse_define(string()) -> {atom(), string()}.
parse_define(S) ->
    case string:split(string:strip(S), "=") of
        [Name] -> {list_to_atom(Name), ""};
        [Name | Val] -> {list_to_atom(Name), Val}
    end.

-spec parse_args([string()]) -> #opts{}.
parse_args(Args) ->
    OptSpecList =
        [
         {espresso_root, $E,    "espresso-root",  string,
             "Path to the root of the espresso binary. Etylizer executes that binary as " ++
             "$ESPRESSO_DIR/espresso. Default root is the escript folder."},
         {project_root, $P,    "project-root",  string,
             "Path to the root of the project. Etylizer stores persistent information in " ++
             "$PROJECT_DIR/_etylizer."},
         {src_path,    $S,    "src-path",       string,
             "Path to a directory containing source files. All .erl files within this " ++
             "directory are type checked, but the directory is not search recursively for " ++
             ".erl files. May be given multiple times. Source files explicitly given " ++
             "on the commandline are added to files found via --source-path."},
         {include,    $I,   "include",   string,
             "Where to search for include files (.hrl). May be given multiple times."  },
         {define,     $D,   "define",    string,
             "Define macro (either '-D NAME' or '-D NAME=VALUE')"},
         {load_start, $a,   "pa",        string,
             "Add path to the front of Erlang's code path"},
         {load_end,   $z,   "pz",        string,
             "Add path to the end of Erlang's code path"},
         {force,       $f,   "force",      undefined,
            "Force type-checking"},
         {help,       $h,   "help",      undefined,
            "Output help message"},
         {check_ast,  $c,   "check-ast", string,
            "Check that all files match the AST type defined in the file given"},
         {dump_raw,  undefined, "dump-raw", undefined,
            "Dump the raw ast (directly after parsing) of the files given"},
         {dump,  $d,   "dump", undefined,
            "Dump the internal ast of the files given"},
         {sanity, undefined, "sanity", undefined,
            "Perform sanity checks"},
         {no_type_checking, undefined, "no-type-checking", undefined,
            "Do not perform type cecking at all"},
         {report_mode, undefined, "report-mode", string,
            "Choose a different mode of error reporting. The default 'early-exit' stops on the first type error encountered, " ++
            "the 'report' mode continues and prints all results at the end to the console (early-exit, report)"},
         {report_timeout, undefined, "report-timeout", string,
            "Define a timeout in milliseconds for type checking a function in report_mode 'report'." ++
            "Default timeout is 5000 milliseconds."},
         {exhaustiveness_mode, undefined, "exhaustiveness-mode", string,
            "Change the mode of how to check for exhaustiveness. Currently, " ++
            "the checker can either globally enable or disable exhaustiveness." ++
            "Default: enabled (enabled, disabled)."},
         {only, $o, "only", string,
            "Only type check these functions (given as module:name/arity or name/arity or just the name)"},
         {ignore, $i, "ignore", string,
            "Do not type check these functions (given as module:name/arity or just name/arity or just the name)"},
         {no_deps, undefined, "no-deps", undefined,
            "Only type check files specified on the commandline (either via --source-path or " ++
            "FILES arguments). The default behavior is to also check the dependencies of these " ++
            "files."},
         {log_level,  $l,   "level",    string,
            "Minimal log level (trace2,trace,debug,info,note,warn)"},
         {type_overlay, undefined, "type-overlay", string,
            "Overlays for fun and type specs"}
        ],
    Opts = case getopt:parse(OptSpecList, Args) of
        {error, {Reason, Data}} ->
            utils:quit(1, "Invalid commandline options: ~p ~p~n", [Reason, Data]);
        {ok, {OptList, RestArgs}} ->
            lists:foldl(
                fun(O, Opts) ->
                    case O of
                        {log_level, S} ->
                            case log:parse_level(S) of
                                bad_log_level -> utils:quit(2, "Invalid log level: " ++ S ++ "~n");
                                L -> Opts#opts{ log_level = L }
                            end;
                        {define, S} ->
                            Opts#opts{ defines = Opts#opts.defines ++ [parse_define(S)] };
                        {load_start, S} ->
                            Opts#opts{ load_start = [S | Opts#opts.load_start] };
                        {load_end, S} ->
                            Opts#opts{ load_end = Opts#opts.load_end ++ [S] };
                        {check_ast, S} -> Opts#opts{ ast_file = S };
                        {espresso_root, S} -> Opts#opts{ espresso_root = S };
                        {project_root, S} -> Opts#opts{ project_root = S };
                        {src_path, F} -> Opts#opts{ src_paths = Opts#opts.src_paths ++ [F]};
                        {include, F} -> Opts#opts{ includes = Opts#opts.includes ++ [F]};
                        {only, S} -> Opts#opts { type_check_only = Opts#opts.type_check_only ++ [S]};
                        {ignore, S} -> Opts#opts { type_check_ignore = Opts#opts.type_check_ignore ++ [S]};
                        dump_raw -> Opts#opts{ dump_raw = true };
                        dump -> Opts#opts{ dump = true };
                        sanity -> Opts#opts{ sanity = true };
                        force -> Opts#opts{ force = true };
                        no_type_checking -> Opts#opts{ no_type_checking = true };
                        {report_mode, "early-exit"} -> Opts#opts{ report_mode = early_exit };
                        {report_mode, "report"} -> Opts#opts{ report_mode = report };
                        {report_mode, M} -> utils:quit(2, "Invalid report mode: " ++ M ++ "~n");
                        {report_timeout, T} -> Parsed = list_to_integer(T), true = Parsed > 0, Opts#opts{ report_timeout = Parsed };
                        {exhaustiveness_mode, "enabled"} -> Opts#opts{ exhaustiveness_mode = enabled };
                        {exhaustiveness_mode, "disabled"} -> Opts#opts{ exhaustiveness_mode = disabled };
                        {exhaustiveness_mode, M} -> utils:quit(2, "Invalid exhaustiveness mode: " ++ M ++ "~n");
                        no_deps -> Opts#opts{ no_deps = true };
                        {type_overlay, S} -> Opts#opts{ type_overlay = S };
                        help -> Opts#opts{ help = true }
                    end
                end, #opts{ files = RestArgs}, OptList)
    end,
    if
        Opts#opts.help ->
            getopt:usage(OptSpecList, "etylizer", "[FILES ...]"),
            utils:quit(2, "Aborting~n");
        true -> ok
    end,
    Opts.

% FIXME (sw, 2023-07-04): this is ugly global state. Remove!
-spec fix_load_path(#opts{}) -> true.
fix_load_path(Opts) ->
    case {Opts#opts.load_start, Opts#opts.load_end} of
        {[], []} -> true;
        {Start, End} ->
            Path = Start ++ [D || D <- code:get_path(), D =/= "."] ++ End,
            true = code:set_path(Path),
            true
    end.

-spec doWork(#opts{}) -> [file:filename()].
doWork(Opts) ->
    % erlang_types needs to know the path of espresso
    % save that in persistent_term
    persistent_term:put(espresso_root, Opts#opts.espresso_root),

    global_state:with_new_state(fun() ->
      ?LOG_TRACE("Check if espresso executable is available"),
      {ok, _} = file:read_file_info(get_espresso_binary()),

      ?LOG_INFO("Initializing ETS tables"),
      parse_cache:init(Opts),
      stdtypes:init(),
      try
          fix_load_path(Opts),
          case Opts#opts.ast_file of
              empty -> ok;
              AstPath ->
                  {Spec, Module} = ast_check:parse_spec(AstPath),
                  ParseOpts = #parse_opts{
                      includes = Opts#opts.includes,
                      defines = Opts#opts.defines
                  },
                  lists:foreach(fun(F) ->
                      ast_check:check(Spec, Module, F, ParseOpts)
                  end, Opts#opts.files),
                  erlang:halt(0)
          end,
          SourceList = paths:generate_input_file_list(Opts),
          SearchPath = paths:compute_search_path(Opts),
          DepGraph =
              case Opts#opts.no_deps of
                  true ->
                      % only typecheck the files given
                      cm_depgraph:new(SourceList);
                  false ->
                      ?LOG_NOTE("Entry points: ~p, now building dependency graph", SourceList),
                      G = cm_depgraph:build_dep_graph(
                          SourceList,
                          SearchPath),
                      ?LOG_DEBUG("Reverse dependency graph: ~p", cm_depgraph:pretty_depgraph(G)),
                      G
              end,
          ?LOG_INFO("Performing type checking"),
          cm_check:perform_type_checks(SearchPath, cm_depgraph:all_sources(DepGraph), DepGraph, Opts)
      after
          parse_cache:cleanup(),
          stdtypes:cleanup()
      end
                                end).

% different path for testing environment
-ifdef(TEST).
get_espresso_binary() ->
    Path = "_build/espresso",
    {ok, _} = file:read_file_info(Path),
    Path.
-else.
get_espresso_binary() ->
    Path = case (catch persistent_term:get(espresso_root)) of
        {_, _} -> filename:join([filename:dirname(escript:script_name()), "espresso"]); % default
        empty -> filename:join([filename:dirname(escript:script_name()), "espresso"]); % default
        Root -> filename:join([Root, "espresso"])
    end,
    {ok, _} = file:read_file_info(Path),
    Path.
-endif.

-spec main([string()]) -> ok.
main(Args) ->
    Opts = parse_args(Args),
    log:init(Opts#opts.log_level),
    ?LOG_INFO("Parsed commandline options as ~200p", Opts),
    try doWork(Opts)
    catch throw:{etylizer, K, Msg}:S ->
            Raw = erl_error:format_exception(throw, K, S),
            IsExpected =
                case K of
                    ty_error -> true;
                    name_error -> true;
                    parse_error -> true;
                    _ -> false
                end,
            if
                IsExpected ->
                    ?LOG_DEBUG("~s", Raw),
                    io:format("~s~n", [Msg]);
                true ->
                    ?LOG_ERROR("~s", Raw),
                    io:format("~s~n", [Msg])
            end,
            case K of
              ty_error -> erlang:halt(1);
              name_error -> erlang:halt(1);
              parse_error -> erlang:halt(1);
              unsupported -> erlang:halt(5);
              not_implemented -> erlang:halt(5);
              _ -> erlang:halt(2)
            end
    end,
    ok.
