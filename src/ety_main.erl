-module(ety_main).
-export([main/1, debug/0]).

% @doc This is the main module of ety. It parses commandline arguments and orchestrates
% everything.

-include_lib("log.hrl").
-include_lib("parse.hrl").
-include_lib("ety_main.hrl").

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
         {project_root, $P,    "project-root",  string,
             "Path to the root of the project"},
         {src_path,    $S,    "src-path",       string,
             "Path to a directory containing source files to be checked"},
         {include,    $I,   "include",   string,
             "Where to search for include files"  },
         {define,     $D,   "define",    string,
             "Define macro (either '-D NAME' or '-D NAME=VALUE')"},
         {load_start, $a,   "pa",        string,
             "Add path to the front of Erlang's code path"},
         {load_end,   $z,   "pz",        string,
             "Add path to the end of Erlang's code path"},
         {check_ast,  $c,   "check-ast", string,
            "Check that all files match the AST type defined in the file given"},
         {dump_raw,  undefined, "dump-raw", undefined,
            "Dump the raw ast (directly after parsing) of the files given"},
         {dump,  $d,   "dump", undefined,
            "Dump the internal ast of the files given"},
         {sanity, undefined, "sanity", undefined,
            "Perform sanity checks"},
         {no_type_checking, undefined, "no-type-checking", undefined,
            "Do not perform type cecking"},
         {only, $o, "only", string,
            "Only typecheck these functions (given as name/arity or just the name)"},
         {log_level,  $l,   "level",    string,
            "Minimal log level (trace,debug,info,note,warn)"},
         {help,       $h,   "help",      undefined,
            "Output help message"}
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
                                bad_log_level -> utils:quit(1, "Invalid log level: ~s", S);
                                L -> Opts#opts{ log_level = L }
                            end;
                        {define, S} ->
                            Opts#opts{ defines = Opts#opts.defines ++ [parse_define(S)] };
                        {load_start, S} ->
                            Opts#opts{ load_start = [S | Opts#opts.load_start] };
                        {load_end, S} ->
                            Opts#opts{ load_end = Opts#opts.load_end ++ [S] };
                        {check_ast, S} -> Opts#opts{ ast_file = S };
                        {project_root, S} -> Opts#opts{ project_root = S };
                        {src_path, F} -> Opts#opts{ src_paths = Opts#opts.src_paths ++ [F]};
                        {include, F} -> Opts#opts{ includes = Opts#opts.includes ++ [F]};
                        {only, S} -> Opts#opts { only = Opts#opts.only ++ [S]};
                        dump_raw -> Opts#opts{ dump_raw = true };
                        dump -> Opts#opts{ dump = true };
                        sanity -> Opts#opts{ sanity = true };
                        no_type_checking -> Opts#opts{ no_type_checking = true };
                        help -> Opts#opts{ help = true }
                    end
                end, #opts{ files = RestArgs}, OptList)
    end,
    if
        Opts#opts.help ->
            getopt:usage(OptSpecList, "ety"),
            utils:quit(1, "Aborting");
        true -> ok
    end,
    Opts.

-spec fix_load_path(#opts{}) -> true.
fix_load_path(Opts) ->
    Path = Opts#opts.load_start ++ [D || D <- code:get_path(), D =/= "."] ++ Opts#opts.load_end,
    true = code:set_path(Path).

-spec doWork(#opts{}) -> ok.
doWork(Opts) ->
    fix_load_path(Opts),
    ParseOpts = #parse_opts{
        includes = Opts#opts.includes,
        defines = Opts#opts.defines
    },
    case Opts#opts.ast_file of
        empty -> ok;
        AstPath ->
            {Spec, Module} = ast_check:parse_spec(AstPath),
            lists:foreach(fun(F) ->
                ast_check:check(Spec, Module, F, ParseOpts)
            end, Opts#opts.files),
            erlang:halt(0)
    end,

    ets:new(forms_table, [set, named_table, {keypos, 1}]),

    SourceList = paths:generate_file_list(Opts),
    DependencyGraph = build_dependency_graph(SourceList, maps:new(), Opts, ParseOpts),

    case Opts#opts.no_type_checking of
        true ->
            ?LOG_NOTE("Not performing type checking as requested"),
            erlang:halt();
        false -> ok
    end,

    cm_check:perform_type_checks(SourceList, symtab:std_symtab(), Opts, DependencyGraph).

-spec build_dependency_graph([file:filename()], cm_depgraph:dependency_graph(), #opts{}, tuple()) -> cm_depgraph:dependency_graph().
build_dependency_graph([CurrentFile | RemainingFiles], DependencyGraph, Opts, ParseOpts) ->
    ?LOG_NOTE("Parsing ~s ...", CurrentFile),
    RawForms = parse:parse_file_or_die(CurrentFile, ParseOpts),
    if  Opts#opts.dump_raw -> ?LOG_NOTE("Raw forms in ~s:~n~p", CurrentFile, RawForms);
        true -> ok
    end,
    ?LOG_TRACE("Parse result (raw):~n~120p", RawForms),

    if Opts#opts.sanity ->
            ?LOG_INFO("Checking whether parse result conforms to AST in ast_erl.erl ..."),
            {RawSpec, _} = ast_check:parse_spec("src/ast_erl.erl"),
            case ast_check:check_against_type(RawSpec, ast_erl, forms, RawForms) of
                true ->
                    ?LOG_INFO("Parse result from ~s conforms to AST in ast_erl.erl", CurrentFile);
                false ->
                    ?ABORT("Parse result from ~s violates AST in ast_erl.erl", CurrentFile)
            end;
       true -> ok
    end,

    ?LOG_NOTE("Transforming ~s ...", CurrentFile),
    Forms = ast_transform:trans(CurrentFile, RawForms),
    if  Opts#opts.dump ->
            ?LOG_NOTE("Transformed forms in ~s:~n~p", CurrentFile, ast_utils:remove_locs(Forms));
        true -> ok
    end,
    ?LOG_TRACE("Parse result (after transform):~n~120p", Forms),

    ets:insert(forms_table, {CurrentFile, Forms}),

    NewDependencyGraph = cm_depgraph:update_dependency_graph(CurrentFile, Forms, RemainingFiles, DependencyGraph),
    build_dependency_graph(RemainingFiles, NewDependencyGraph, Opts, ParseOpts);

build_dependency_graph([], DependencyGraph, _, _) ->
    DependencyGraph.

-spec main([string()]) -> ok.
main(Args) ->
    Opts = parse_args(Args),
    log:init(Opts#opts.log_level),
    ?LOG_INFO("Parsed commandline options as ~200p", Opts),
    try doWork(Opts)
    catch throw:{ety, K, Msg}:S ->
            Raw = erl_error:format_exception(throw, K, S),
            ?LOG_ERROR("~s", Raw),
            io:format("~s~n", [Msg]),
            erlang:halt(1)
    end.

debug() ->
  Args = ["--level","debug","--sanity","--only","catch_01/0",
      "test_files/tycheck_simple.erl"],
  Opts = parse_args(Args),
  log:init(Opts#opts.log_level),
  ?LOG_INFO("Parsed commandline options as ~200p", Opts),
  try doWork(Opts)
  catch throw:{ety, K, Msg}:S ->
    Raw = erl_error:format_exception(throw, K, S),
    ?LOG_INFO("~s", Raw),
    io:format("~s~n", [Msg]),
    erlang:halt(1)
  end.
