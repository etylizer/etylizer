-module(etylizer_main).
-export([
    main/1,
    doWork/1
]).



% @doc This is the main module of etylizer. It parses commandline arguments and orchestrates
% everything.

-include("log.hrl").
-include("parse.hrl").
-include("etylizer_main.hrl").
-include("etylizer.hrl").

-spec parse_define(string()) -> {atom(), string()}.
parse_define(S) ->
    case string:split(string:strip(S), "=") of
        [Name, Val] -> {list_to_atom(Name), Val};
        [Name] -> {list_to_atom(Name), ""};
        _ -> erlang:error({bad_define, S})
    end.

-spec cmd_spec() -> argparse:command().
cmd_spec() ->
    ?assert_type(#{
        arguments => [
            #{name => espresso_root, short => $E, long => "-espresso-root",
              help => "Path to the root of the espresso binary. Default root is the escript folder."},
            #{name => project_root, short => $P, long => "-project-root",
              help => "Path to the root of the project. Stores persistent information in $PROJECT_DIR/_etylizer."},
            #{name => src_path, short => $S, long => "-src-path", action => append,
              help => "Path to a directory containing source files. May be given multiple times."},
            #{name => include, short => $I, long => "-include", action => append,
              help => "Where to search for include files (.hrl). May be given multiple times."},
            #{name => define, short => $D, long => "-define", action => append,
              help => "Define macro (either '-D NAME' or '-D NAME=VALUE')"},
            #{name => load_start, short => $a, long => "-pa", action => append,
              help => "Add path to the front of Erlang's code path"},
            #{name => load_end, short => $z, long => "-pz", action => append,
              help => "Add path to the end of Erlang's code path"},
            #{name => force, short => $f, long => "-force", type => boolean, default => false,
              help => "Force type-checking"},
            #{name => help, short => $h, long => "-help", type => boolean, default => false,
              help => "Output help message"},
            #{name => check_ast, short => $c, long => "-check-ast",
              help => "Check that all files match the AST type defined in the file given"},
            #{name => dump_raw, long => "-dump-raw", type => boolean, default => false,
              help => "Dump the raw ast (directly after parsing) of the files given"},
            #{name => dump, short => $d, long => "-dump", type => boolean, default => false,
              help => "Dump the internal ast of the files given"},
            #{name => sanity, long => "-sanity", type => boolean, default => false,
              help => "Perform sanity checks"},
            #{name => sanity_inference, long => "-sanity-inference", type => boolean, default => false,
              help => "After checking, also infer types and verify that inferred types are more general than specs"},
            #{name => no_type_checking, long => "-no-type-checking", type => boolean, default => false,
              help => "Do not perform type checking at all"},
            #{name => report_mode, long => "-report-mode", type => {string, ["early-exit", "report"]},
              help => "Error reporting mode (early-exit, report). Default: early-exit"},
            #{name => report_timeout, long => "-report-timeout", type => {integer, [{min, 1}]},
              default => 5000,
              help => "Timeout in ms for type checking a function in report mode. Default: 5000"},
            #{name => exhaustiveness_mode, long => "-exhaustiveness-mode",
              type => {string, ["enabled", "disabled"]},
              help => "Enable or disable exhaustiveness checking. Default: enabled"},
            #{name => gradual_mode, long => "-gradual-mode", type => {string, ["dynamic", "infer"]},
              help => "How to handle functions without type specs. Default: dynamic"},
            #{name => only, short => $o, long => "-only", action => append,
              help => "Only type check these functions (module:name/arity or name/arity or name)"},
            #{name => ignore, short => $i, long => "-ignore", action => append,
              help => "Do not type check these functions (module:name/arity or name/arity or name)"},
            #{name => no_deps, long => "-no-deps", type => boolean, default => false,
              help => "Only type check files specified on the commandline"},
            #{name => log_level, short => $l, long => "-level",
              help => "Minimal log level (trace2,trace,debug,info,note,warn)"},
            #{name => log_file, long => "-log-file",
              help => "Path to the log file (default: etylizer.log)"},
            #{name => type_overlay, long => "-type-overlay",
              help => "Overlays for fun and type specs"},
            #{name => check_exports, long => "-check-exports", type => boolean, default => false,
              help => "Check that all exported functions have a type spec."},
            #{name => files, nargs => list, required => false, default => [],
              help => "Files to type check"}
        ]
    }, argparse:command()).

-spec parse_args([string()]) -> #opts{}.
parse_args(Args) ->
    Command = cmd_spec(),
    ParseOpts = #{progname => "etylizer"},
    ArgMap = case argparse:parse(Args, Command, ParseOpts) of
        {error, Reason} ->
            io:format("~ts~n", [argparse:format_error(Reason)]),
            utils:quit(1, "Invalid commandline options~n");
        {ok, AM, _, _} ->
            AM
    end,
    case ?assert_type(maps:get(help, ArgMap, false), boolean()) of
        true ->
            io:format("~ts", [argparse:help(Command, ParseOpts)]),
            utils:quit(2, "Aborting~n");
        false -> ok
    end,
    build_opts(ArgMap).

-spec parse_log_level(argparse:arg_map()) -> log:log_level() | default.
parse_log_level(ArgMap) ->
    case maps:find(log_level, ArgMap) of
        {ok, Val} ->
            S = ?assert_type(Val, string()),
            case log:parse_level(S) of
                bad_log_level -> utils:quit(2, "Invalid log level: " ++ S ++ "~n");
                L -> L
            end;
        error -> default
    end.

-spec parse_report_mode(argparse:arg_map()) -> feature_flags:report_mode().
parse_report_mode(ArgMap) ->
    case ?assert_type(maps:get(report_mode, ArgMap, "early-exit"), string()) of
        "early-exit" -> early_exit;
        "report" -> report;
        _ -> erlang:error(bad_report_mode)
    end.

-spec parse_exhaustiveness_mode(argparse:arg_map()) -> feature_flags:exhaustiveness_mode().
parse_exhaustiveness_mode(ArgMap) ->
    case ?assert_type(maps:get(exhaustiveness_mode, ArgMap, "enabled"), string()) of
        "enabled" -> enabled;
        "disabled" -> disabled;
        _ -> erlang:error(bad_exhaustiveness_mode)
    end.

-spec parse_gradual_mode(argparse:arg_map()) -> feature_flags:gradual_typing_mode().
parse_gradual_mode(ArgMap) ->
    case ?assert_type(maps:get(gradual_mode, ArgMap, "dynamic"), string()) of
        "dynamic" -> dynamic;
        "infer" -> infer;
        _ -> erlang:error(bad_gradual_mode)
    end.

-spec build_opts(argparse:arg_map()) -> #opts{}.
build_opts(ArgMap) ->
    LogLevel = parse_log_level(ArgMap),
    ReportMode = parse_report_mode(ArgMap),
    ExhaustivenessMode = parse_exhaustiveness_mode(ArgMap),
    GradualMode = parse_gradual_mode(ArgMap),
    #opts{
        log_level = LogLevel,
        log_file = ?assert_type(maps:get(log_file, ArgMap, "etylizer.log"), string()),
        dump_raw = ?assert_type(maps:get(dump_raw, ArgMap, false), boolean()),
        dump = ?assert_type(maps:get(dump, ArgMap, false), boolean()),
        sanity = ?assert_type(maps:get(sanity, ArgMap, false), boolean()),
        sanity_infer = ?assert_type(maps:get(sanity_inference, ArgMap, false), boolean()),
        force = ?assert_type(maps:get(force, ArgMap, false), boolean()),
        no_type_checking = ?assert_type(maps:get(no_type_checking, ArgMap, false), boolean()),
        report_mode = ReportMode,
        report_timeout = ?assert_type(maps:get(report_timeout, ArgMap, 5000), pos_integer()),
        exhaustiveness_mode = ExhaustivenessMode,
        gradual_typing_mode = GradualMode,
        no_deps = ?assert_type(maps:get(no_deps, ArgMap, false), boolean()),
        check_exports = ?assert_type(maps:get(check_exports, ArgMap, false), boolean()),
        type_check_only = ?assert_type(maps:get(only, ArgMap, []), [string()]),
        type_check_ignore = ?assert_type(maps:get(ignore, ArgMap, []), [string()]),
        ast_file = ?assert_type(maps:get(check_ast, ArgMap, empty), empty | string()),
        project_root = ?assert_type(maps:get(project_root, ArgMap, empty), empty | string()),
        espresso_root = ?assert_type(maps:get(espresso_root, ArgMap, empty), empty | string()),
        src_paths = ?assert_type(maps:get(src_path, ArgMap, []), [string()]),
        includes = ?assert_type(maps:get(include, ArgMap, []), [string()]),
        defines = [parse_define(D) || D <- ?assert_type(maps:get(define, ArgMap, []), [string()])],
        load_start = ?assert_type(maps:get(load_start, ArgMap, []), [string()]),
        load_end = ?assert_type(maps:get(load_end, ArgMap, []), [string()]),
        files = ?assert_type(maps:get(files, ArgMap, []), [string()]),
        type_overlay = ?assert_type(maps:get(type_overlay, ArgMap, []), string())
    }.

% FIXME (sw, 2023-07-04): this is ugly global state. Remove!
-spec fix_load_path(#opts{}) -> true.
fix_load_path(Opts) ->
    case {Opts#opts.load_start, Opts#opts.load_end} of
        {[], []} -> true;
        {Start, End} ->
            Path = Start ++ [D || D <- code:get_path(), D =/= "."] ++ End,
            ?assert_pattern(true, code:set_path(Path)),
            true
    end.

-spec doWork(#opts{}) -> [file:filename()].
doWork(Opts) ->
    ?assert_type(global_state:with_new_state(fun() ->
      ?LOG_TRACE("Initializing ETS tables"),
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
                      ?LOG_DEBUG("Entry points: ~p, now building dependency graph", SourceList),
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
                                end), [file:filename()]).


-spec main([string()]) -> ok.
main(Args) ->
    Opts = parse_args(Args),
    log:init(Opts#opts.log_level, Opts#opts.log_file),
    ?LOG_DEBUG("Parsed commandline options as ~200p", Opts),
    main_run(Opts).

-spec main_run(#opts{}) -> ok.
main_run(Opts) ->
    try doWork(Opts)
    catch throw:Thrown:S ->
        {etylizer, K, Msg} = ?assert_type(Thrown, {etylizer, atom(), string()}),
        handle_main_error(K, Msg, ?assert_type(S, erlang:stacktrace()))
    end,
    ok.

-spec handle_main_error(atom(), string(), erlang:stacktrace()) -> no_return().
handle_main_error(K, Msg, S) ->
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
    end.
