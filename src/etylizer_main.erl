-module(etylizer_main).
-export([
    main/1
]).

-ifdef(TEST).
-export([
    doWork/1
]).
-endif.


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

-spec cmd_spec() -> argparse:command().
cmd_spec() ->
    #{
        arguments => [
            #{name => espresso_root, short => $E, long => "-espresso-root",
              help => "Path to the root of the espresso binary. Etylizer executes that binary as "
                      "$ESPRESSO_DIR/espresso. Default root is the escript folder."},
            #{name => project_root, short => $P, long => "-project-root",
              help => "Path to the root of the project. Etylizer stores persistent information in "
                      "$PROJECT_DIR/_etylizer."},
            #{name => src_path, short => $S, long => "-src-path", action => append, default => [],
              help => "Path to a directory containing source files. All .erl files within this "
                      "directory are type checked, but the directory is not search recursively for "
                      ".erl files. May be given multiple times. Source files explicitly given "
                      "on the commandline are added to files found via --source-path."},
            #{name => include, short => $I, long => "-include", action => append, default => [],
              help => "Where to search for include files (.hrl). May be given multiple times."},
            #{name => define, short => $D, long => "-define", action => append, default => [],
              help => "Define macro (either '-D NAME' or '-D NAME=VALUE')"},
            #{name => load_start, short => $a, long => "-pa", action => append, default => [],
              help => "Add path to the front of Erlang's code path"},
            #{name => load_end, short => $z, long => "-pz", action => append, default => [],
              help => "Add path to the end of Erlang's code path"},
            #{name => force, short => $f, long => "-force", type => boolean, default => false,
              help => "Force type-checking"},
            #{name => help, short => $h, long => "-help", type => boolean, default => false,
              help => "Output help message"},
            #{name => version, long => "-version", type => boolean, default => false,
              help => "Display version and exit"},
            #{name => check_ast, short => $c, long => "-check-ast",
              help => "Check that all files match the AST type defined in the file given"},
            #{name => dump_raw, long => "-dump-raw", type => boolean, default => false,
              help => "Dump the raw ast (directly after parsing) of the files given"},
            #{name => dump, short => $d, long => "-dump", type => boolean, default => false,
              help => "Dump the internal ast of the files given"},
            #{name => dump_transformed, long => "-dump-transformed-ast", type => boolean, default => false,
              help => "Dump functions after clause-to-case transformation (use -o to filter)"},
            #{name => sanity, long => "-sanity", type => boolean, default => false,
              help => "Perform sanity checks"},
            #{name => no_type_checking, long => "-no-type-checking", type => boolean, default => false,
              help => "Do not perform type cecking at all"},
            #{name => report_mode, long => "-report-mode",
              type => {custom, fun("early-exit") -> early_exit;
                                  ("report") -> report;
                                  (_) -> error(badarg)
                       end},
              default => early_exit,
              help => "Choose a different mode of error reporting. The default 'early-exit' stops "
                      "on the first type error encountered, the 'report' mode continues and prints "
                      "all results at the end to the console (early-exit, report)"},
            #{name => report_timeout, long => "-report-timeout", type => {integer, [{min, 1}]},
              default => 5000,
              help => "Define a timeout in milliseconds for type checking a function in report_mode 'report'."
                      "Default timeout is 5000 milliseconds."},
            #{name => exhaustiveness_mode, long => "-exhaustiveness-mode",
              type => {custom, fun("enabled") -> enabled;
                                  ("disabled") -> disabled;
                                  (_) -> error(badarg)
                       end},
              default => enabled,
              help => "Change the mode of how to check for exhaustiveness. "
                      "The checker can either globally enable or disable exhaustiveness with this flag."
                      "Default: enabled (enabled, disabled)."},
            #{name => gradual_mode, long => "-gradual-mode",
              type => {custom, fun("dynamic") -> dynamic;
                                  ("infer") -> infer;
                                  (_) -> error(badarg)
                       end},
              default => dynamic,
              help => "Choose how to handle functions without type specs. "
                      "'dynamic' assigns dynamic types, 'infer' infers types. "
                      "Default: dynamic (dynamic, infer)."},
            #{name => only, short => $o, long => "-only", action => append, default => [],
              help => "Only type check these functions (given as module:name/arity or name/arity or just the name)"},
            #{name => ignore, short => $i, long => "-ignore", action => append, default => [],
              help => "Do not type check these functions (given as module:name/arity or just name/arity or just the name)"},
            #{name => no_deps, long => "-no-deps", type => boolean, default => false,
              help => "Only type check files specified on the commandline (either via --source-path or "
                      "FILES arguments). The default behavior is to also check the dependencies of these "
                      "files."},
            #{name => log_level, short => $l, long => "-level",
              type => {custom, fun(S) ->
                  case log:parse_level(S) of
                      bad_log_level -> error(badarg);
                      L -> L
                  end
              end},
              help => "Minimal log level (trace2,trace,debug,info,note,warn)"},
            #{name => log_file, long => "-log-file",
              help => "Path to the log file (default: etylizer.log)"},
            #{name => type_overlay, long => "-type-overlay",
              help => "Overlays for fun and type specs"},
            #{name => check_exports, long => "-check-exports", type => boolean, default => false,
              help => "Check that all exported functions have a type spec."},
            #{name => no_exhaustiveness, long => "-no-exhaustiveness", action => append, default => [],
              help => "Disable exhaustiveness checking for a function (name/arity). May be given multiple times."},
            #{name => no_redundancy, long => "-no-redundancy", action => append, default => [],
              help => "Disable redundancy checking for a function (name/arity). May be given multiple times."},
            #{name => verbose, short => $v, long => "-verbose", type => boolean, default => false,
              help => "Verbose output (e.g. preprocessor warnings)"},
            #{name => metrics_file, long => "-metrics-file",
              help => "Write collected metrics to the given JSON file"},
            #{name => files, nargs => list, required => false, default => [],
              help => "Files to type check"}
        ]
    }.

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
    Opts = #opts{
        help = maps:get(help, ArgMap),
        version = maps:get(version, ArgMap, false),
        log_level = maps:get(log_level, ArgMap, default),
        log_file = maps:get(log_file, ArgMap, "etylizer.log"),
        dump_raw = maps:get(dump_raw, ArgMap),
        dump = maps:get(dump, ArgMap),
        dump_transformed = maps:get(dump_transformed, ArgMap),
        sanity = maps:get(sanity, ArgMap),
        force = maps:get(force, ArgMap),
        no_type_checking = maps:get(no_type_checking, ArgMap),
        report_mode = maps:get(report_mode, ArgMap),
        report_timeout = maps:get(report_timeout, ArgMap),
        exhaustiveness_mode = maps:get(exhaustiveness_mode, ArgMap),
        gradual_typing_mode = maps:get(gradual_mode, ArgMap),
        no_deps = maps:get(no_deps, ArgMap),
        check_exports = maps:get(check_exports, ArgMap),
        type_check_only = maps:get(only, ArgMap),
        type_check_ignore = maps:get(ignore, ArgMap),
        ast_file = maps:get(check_ast, ArgMap, empty),
        project_root = maps:get(project_root, ArgMap, empty),
        espresso_root = maps:get(espresso_root, ArgMap, empty),
        src_paths = maps:get(src_path, ArgMap),
        includes = maps:get(include, ArgMap),
        defines = [parse_define(D) || D <- maps:get(define, ArgMap)],
        load_start = maps:get(load_start, ArgMap),
        load_end = maps:get(load_end, ArgMap),
        no_exhaustiveness = maps:get(no_exhaustiveness, ArgMap),
        no_redundancy = maps:get(no_redundancy, ArgMap),
        files = maps:get(files, ArgMap),
        type_overlay = maps:get(type_overlay, ArgMap, []),
        verbose = maps:get(verbose, ArgMap, false),
        metrics_file = maps:get(metrics_file, ArgMap, undefined)
    },
    if
        Opts#opts.help ->
            io:format("~ts", [argparse:help(Command, ParseOpts)]),
            utils:quit(0, "");
        true -> ok
    end,
    case Opts#opts.version of
        true ->
            ok = application:load(etylizer),
            {ok, Vsn} = application:get_key(etylizer, vsn),
            io:format("etylizer ~s~n", [Vsn]),
            utils:quit(0, "");
        false -> ok
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

-spec dump_transformed_ast(#opts{}) -> ok.
dump_transformed_ast(Opts) ->
    Only = sets:from_list(Opts#opts.type_check_only),
    lists:foreach(fun(File) ->
        Forms = parse_cache:parse(intern, File),
        FunDecls = [F || F = {function, _, _, _, _} <- Forms],
        ModName = ast_utils:modname_from_path(File),
        lists:foreach(fun({function, L, Name, Arity, FunClauses}) ->
            RefStr = utils:sformat("~w/~w", Name, Arity),
            QRefStr = utils:sformat("~w:~s", ModName, RefStr),
            NameStr = utils:sformat("~w", Name),
            ModStr = utils:sformat("~w", ModName),
            ShouldDump = case sets:is_empty(Only) of
                true -> true;
                false ->
                    sets:is_element(QRefStr, Only)
                    orelse sets:is_element(RefStr, Only)
                    orelse sets:is_element(NameStr, Only)
                    orelse sets:is_element(ModStr, Only)
            end,
            case ShouldDump of
                false -> ok;
                true ->
                    Ctx = constr_gen:new_ctx(symtab:empty(), enabled),
                    {Args, Body} = constr_gen:fun_clauses_to_exp(Ctx, L, FunClauses),
                    io:format("~s(~s) ->~n", [Name, pretty:render_varnames(Args)]),
                    io:format("~s.~n~n", [pretty:render_exps(Body, 2)])
            end
        end, FunDecls)
    end, Opts#opts.files).

-spec doWork(#opts{}) -> [file:filename()].
doWork(Opts) ->
    global_state:with_new_state(fun() ->
      ?LOG_TRACE("Initializing ETS tables"),
      case Opts#opts.metrics_file of
          undefined -> ok;
          _ -> metrics:init()
      end,
      parse_cache:init(Opts),
      stdtypes:init(),
      try
          fix_load_path(Opts),
          case Opts#opts.ast_file of
              empty -> ok;
              AstPath ->
                  {Spec, Module} = ast_check:parse_spec(AstPath),
                  ParseOpts = #parse_opts{
                      verbose = Opts#opts.verbose,
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
          case Opts#opts.dump_transformed of
              true ->
                  dump_transformed_ast(Opts),
                  [];
              false ->
                  ?LOG_INFO("Performing type checking"),
                  cm_check:perform_type_checks(SearchPath, cm_depgraph:all_sources(DepGraph), DepGraph, Opts)
          end
      after
          case Opts#opts.metrics_file of
              undefined -> ok;
              Path -> metrics:dump(Path)
          end,
          metrics:cleanup(),
          parse_cache:cleanup(),
          stdtypes:cleanup()
      end
                                end).

-spec main([string()]) -> ok.
main(Args) ->
    Opts = parse_args(Args),
    log:init(Opts#opts.log_level, Opts#opts.log_file),
    ?LOG_DEBUG("Parsed commandline options as ~200p", Opts),
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
