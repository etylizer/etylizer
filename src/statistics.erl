-module(statistics).

% Reproduces the *static* metrics reported in the etylizer papers (jfp-2025,
% erlang-2026, icfp-2026) by driving etylizer's own front-end (parse ->
% ast_transform -> symtab -> constr_gen) and walking the resulting internal
% structures, instead of the standalone epp_dodger escripts used in the papers.
%
% It never runs the type checker: type-check outcomes and timing stay with the
% normal `--report-mode report` pipeline. The only static overlap it owns is
% LOC and the number of top-level functions.
%
% This module is the scaffolding: it parses arguments, iterates the input
% modules, acquires the raw and transformed AST for each, and emits a unified
% per-module JSON report. The individual metric collectors are added on top of
% `module_report/2` in later commits.

-include("log.hrl").
-include("parse.hrl").
-include("etylizer_main.hrl").

-export([
    main/1,        % escript entry point
    run/1,         % programmatic entry: #opts{} -> iodata() (JSON)
    module_report/2
]).

-type report() :: #{atom() => term()}.

%% ---------------------------------------------------------------------------
%% Entry points
%% ---------------------------------------------------------------------------

% Escript entry: parse args, produce the JSON report, write it out.
-spec main([string()]) -> ok.
main(Args) ->
    {Opts, OutFile} = parse_args(Args),
    Json = run(Opts),
    case OutFile of
        stdout -> io:format("~s~n", [Json]);
        _ -> ok = file:write_file(OutFile, Json)
    end,
    ok.

% Programmatic entry: given #opts{}, compute the report for every input module
% and return it as encoded JSON (iodata).
-spec run(cmd_opts()) -> iodata().
run(Opts) ->
    global_state:with_new_state(
      fun() ->
          parse_cache:init(Opts),
          stdtypes:init(),
          try
              Files = paths:generate_input_file_list(Opts),
              ?LOG_INFO("Computing statistics for ~w modules", length(Files)),
              Reports = lists:map(fun(F) -> module_report(F, Opts) end, Files),
              json:encode(#{modules => Reports})
          after
              parse_cache:cleanup(),
              stdtypes:cleanup()
          end
      end).

%% ---------------------------------------------------------------------------
%% Per-module driver
%% ---------------------------------------------------------------------------

% Acquire the raw and transformed AST for a single file and run the collectors
% over them. The scaffolding reports only identity and parse status; later
% commits merge the individual collector results into the returned map.
%
% The raw AST is acquired first so that raw-level metrics can still be computed
% even when ast_transform fails on a file.
-spec module_report(file:filename(), cmd_opts()) -> report().
module_report(File, Opts) ->
    ParseOpts = #parse_opts{
        includes = Opts#opts.includes,
        defines = Opts#opts.defines,
        verbose = false
    },
    Base = #{module => ast_utils:modname_from_path(File),
             file => unicode:characters_to_binary(File)},
    case parse:parse_file(File, ParseOpts) of
        error ->
            Base#{parse => parse_failed};
        {ok, RawForms} ->
            RawReport = lists:foldl(fun deep_merge/2, Base#{parse => ok},
                                    raw_collectors(RawForms)),
            case try_transform(File, RawForms) of
                {ok, TxForms} ->
                    lists:foldl(fun deep_merge/2, RawReport, tx_collectors(TxForms));
                error ->
                    RawReport#{parse => transform_failed}
            end
    end.

% Collectors over the raw Erlang AST. Each returns a (possibly nested) map that
% is deep-merged into the module report.
-spec raw_collectors([ast_erl:form()]) -> [report()].
raw_collectors(RawForms) ->
    [collect_corpus(RawForms)].

% Collectors over the transformed (internal) AST.
-spec tx_collectors([ast:form()]) -> [report()].
tx_collectors(_TxForms) ->
    [].

-spec try_transform(file:filename(), [ast_erl:form()]) -> {ok, [ast:form()]} | error.
try_transform(File, RawForms) ->
    try {ok, ast_transform:trans(File, RawForms)}
    catch throw:{etylizer, _Kind, _Msg} -> error end.

%% ---------------------------------------------------------------------------
%% #1 LOC and top-level function count
%% ---------------------------------------------------------------------------

% Number of top-level function declarations (one form per name/arity), plus LOC.
% LOC is the number of non-blank lines produced by pretty-printing the forms with
% Erlang's formatter (erl_pp), which normalizes away comments, blank lines, and
% source formatting. It is therefore only defined for successfully-parsed modules.
-spec collect_corpus([ast_erl:form()]) -> report().
collect_corpus(RawForms) ->
    NFunctions = length([F || F = {function, _, _, _, _} <- RawForms]),
    #{loc => formatted_loc(RawForms),
      corpus => #{n_functions => NFunctions}}.

-spec formatted_loc([ast_erl:form()]) -> non_neg_integer().
formatted_loc(Forms) ->
    lists:sum([form_line_count(F) || F <- Forms]).

% Non-blank lines produced by pretty-printing a single form. Forms erl_pp cannot
% render (e.g. the eof marker) contribute nothing.
-spec form_line_count(ast_erl:form()) -> non_neg_integer().
form_line_count(Form) ->
    try unicode:characters_to_list(erl_pp:form(Form)) of
        Text ->
            length([L || L <- string:split(Text, "\n", all), string:trim(L) =/= ""])
    catch _:_ -> 0
    end.

%% ---------------------------------------------------------------------------
%% Argument parsing
%% ---------------------------------------------------------------------------

% Command-line handling using the same argparse-based method as etylizer_main:
% a command specification, argparse:parse/3, then build the #opts{} record.
-spec cmd_spec() -> argparse:command().
cmd_spec() ->
    #{
        arguments => [
            #{name => project_root, short => $P, long => "-project-root",
              help => "Path to the root of the project. Used to resolve dependencies and the "
                      "search path for call classification."},
            #{name => src_path, short => $S, long => "-src-path", action => append, default => [],
              help => "Directory of source files to analyze (not searched recursively). May be "
                      "given multiple times. Combined with any FILES given on the commandline."},
            #{name => include, short => $I, long => "-include", action => append, default => [],
              help => "Where to search for include files (.hrl). May be given multiple times."},
            #{name => define, short => $D, long => "-define", action => append, default => [],
              help => "Define macro (either '-D NAME' or '-D NAME=VALUE')."},
            #{name => out, long => "-out",
              help => "Write the JSON report to this file (default: stdout)."},
            #{name => help, short => $h, long => "-help", type => boolean, default => false,
              help => "Output help message."},
            #{name => files, nargs => list, required => false, default => [],
              help => "Files to analyze."}
        ]
    }.

-spec parse_args([string()]) -> {cmd_opts(), stdout | file:filename()}.
parse_args(Args) ->
    Command = cmd_spec(),
    ParseOpts = #{progname => "statistics"},
    ArgMap = case argparse:parse(Args, Command, ParseOpts) of
        {error, Reason} ->
            io:format(standard_error, "~ts~n", [argparse:format_error(Reason)]),
            utils:quit(1, "Invalid commandline options~n");
        {ok, AM, _, _} ->
            AM
    end,
    case maps:get(help, ArgMap) of
        true ->
            io:format("~ts", [argparse:help(Command, ParseOpts)]),
            utils:quit(0, "");
        false -> ok
    end,
    Opts = #opts{
        project_root = maps:get(project_root, ArgMap, empty),
        src_paths = maps:get(src_path, ArgMap),
        includes = maps:get(include, ArgMap),
        defines = [parse_define(D) || D <- maps:get(define, ArgMap)],
        files = maps:get(files, ArgMap)
    },
    {Opts, maps:get(out, ArgMap, stdout)}.

-spec parse_define(string()) -> {atom(), string()}.
parse_define(S) ->
    case string:split(string:strip(S), "=") of
        [Name] -> {list_to_atom(Name), ""};
        [Name | Val] -> {list_to_atom(Name), Val}
    end.

% Recursively merge two report maps: nested maps under the same key are merged,
% other values from the second map win. Lets each collector contribute to a
% shared group (e.g. `corpus`, `features`) independently.
-spec deep_merge(report(), report()) -> report().
deep_merge(M1, M2) ->
    maps:fold(
      fun(K, V2, Acc) ->
          case Acc of
              #{K := V1} when is_map(V1), is_map(V2) -> Acc#{K => deep_merge(V1, V2)};
              _ -> Acc#{K => V2}
          end
      end, M1, M2).

%% The report maps are built directly in the shape stdlib `json' accepts (atom
%% keys, atom/integer/binary values, nested maps and lists), so no conversion
%% step is needed. The only value that is not a plain atom/integer is the file
%% path, which is stored as a binary (see module_report/3).
