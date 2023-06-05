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
         {path,       $P,    "path",     string,
             "Path to the project"},
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
                        {path, S} -> Opts#opts{ path = S };
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

    Symtab = symtab:std_symtab(),
    SourceList = generate_file_list(Opts),
    {DependencyGraph, FormsList} = traverse_source_list(SourceList, maps:new(), maps:new(), Opts, ParseOpts),

    case Opts#opts.no_type_checking of
        true ->
            ?LOG_NOTE("Not performing type checking as requested"),
            erlang:halt();
        false -> ok
    end,

    cm_check:perform_type_checks(FormsList, Symtab, Opts, DependencyGraph).

-spec generate_file_list(#opts{}) -> [file:filename()].
generate_file_list(Opts) ->
    case Opts#opts.path of
        empty ->
            case Opts#opts.files of
                [] -> utils:quit(1, "No input files given, aborting");
                Files -> Files
            end;
        Path ->
            add_dir_to_list(Path)
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

-spec traverse_source_list([file:filename()], map(), map(), #opts{}, tuple()) -> tuple().
traverse_source_list(SourceList, DependencyGraph, FormsList, Opts, ParseOpts) ->
    case SourceList of
        [CurrentFile | RemainingFiles] ->
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

            Sanity =
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
                end,

            NewDependencyGraph = dependency_graph:update_dependency_graph(CurrentFile, Forms, RemainingFiles, DependencyGraph),
            NewFormsList = maps:put(CurrentFile, {Forms, Sanity}, FormsList),

            traverse_source_list(RemainingFiles, NewDependencyGraph, NewFormsList, Opts, ParseOpts);
        [] ->
            {DependencyGraph, FormsList}
    end.

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
