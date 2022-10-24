-module(ety_main).
-export([main/1, debug/0]).

% @doc This is the main module of ety. It parses commandline arguments and orchestrates
% everything.

-include_lib("log.hrl").
-include_lib("parse.hrl").

-record(opts, {log_level = default :: log:log_level() | default,
               help = false :: boolean(),
               dump_raw = false :: boolean(),
               dump = false :: boolean(),
               sanity = false :: boolean(),
               no_type_checking = false :: boolean(),
               only = [] :: [string()],
               ast_file = empty :: empty | string(),
               includes = [] :: [string()],
               defines = [] :: [{atom(), string()}],
               load_start = [] :: [string()],
               load_end = [] :: [string()],
               files = [] :: [string()]}).

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
    Files = Opts#opts.files,
    case Files of
        [] -> utils:quit(1, "No input files given, aborting");
        _ -> ok
    end,
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
    lists:foreach(
      fun(F) ->
              ?LOG_NOTE("Parsing ~s ...", F),
              RawForms = parse:parse_file_or_die(F, ParseOpts),
              if  Opts#opts.dump_raw -> ?LOG_NOTE("Raw forms in ~s:~n~p", F, RawForms);
                  true -> ok
              end,
              ?LOG_TRACE("Parse result (raw):~n~120p", RawForms),
              if Opts#opts.sanity ->
                      ?LOG_INFO("Checking whether parse result conforms to AST in ast_erl.erl ..."),
                      {RawSpec, _} = ast_check:parse_spec("src/ast_erl.erl"),
                      case ast_check:check_against_type(RawSpec, ast_erl, forms, RawForms) of
                          true ->
                              ?LOG_INFO("Parse result from ~s conforms to AST in ast_erl.erl", F);
                          false ->
                              ?ABORT("Parse result from ~s violates AST in ast_erl.erl", F)
                      end;
                 true -> ok
              end,
              ?LOG_NOTE("Transforming ~s ...", F),
              Forms = ast_transform:trans(F, RawForms),
              if  Opts#opts.dump ->
                      ?LOG_NOTE("Transformed forms in ~s:~n~p", F, ast_utils:remove_locs(Forms));
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
                                  ?LOG_INFO("Transform result from ~s conforms to AST in ast.erl", F);
                              false ->
                                  ?ABORT("Transform result from ~s violates AST in ast.erl", F)
                          end,
                          {SpecConstr, _} = ast_check:parse_spec("src/constr.erl"),
                          SpecFullConstr = ast_check:merge_specs([SpecConstr, AstSpec]),
                          {ok, SpecFullConstr};
                     true -> error
                  end,
              case Opts#opts.no_type_checking of
                  true -> ?LOG_NOTE("Not performing type checking as requested");
                  false ->
                      ?LOG_NOTE("Typechecking ~s ...", F),
                      Only = sets:from_list(Opts#opts.only),
                      Ctx = typing:new_ctx(Symtab, Sanity),
                      typing:check_forms(Ctx, Forms, Only)
              end
      end, Opts#opts.files).

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
