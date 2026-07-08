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
              Reports = lists:map(fun(F) -> safe_module_report(F, Opts) end, Files),
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
% Wrapper for the file sweep (#8, parse sweep): a single unparseable or
% malformed module must never abort the whole run, so any unexpected crash is
% recorded as `crashed` for that module. The per-module `parse` field is thus
% one of: ok | parse_failed | transform_failed | crashed.
-spec safe_module_report(file:filename(), cmd_opts()) -> report().
safe_module_report(File, Opts) ->
    try module_report(File, Opts)
    catch Class:Reason:Stack ->
        ?LOG_WARN("statistics crashed on ~s: ~p:~p~n~p", [File, Class, Reason, Stack]),
        #{module => ast_utils:modname_from_path(File),
          file => unicode:characters_to_binary(File), parse => crashed}
    end.

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
            %% Count only the module's own forms; the full compiler front-end
            %% inlines -include'd headers, which would otherwise be counted once
            %% per including module. The transform still gets the full forms so
            %% header types/records resolve.
            OwnRaw = own_forms(File, RawForms),
            RawReport = lists:foldl(fun deep_merge/2, Base#{parse => ok},
                                    raw_collectors(OwnRaw)),
            case try_transform(File, RawForms) of
                {ok, TxForms} ->
                    lists:foldl(fun deep_merge/2, RawReport, tx_collectors(TxForms));
                error ->
                    RawReport#{parse => transform_failed}
            end
    end.

% Drop forms pulled in from -include'd headers, keeping only those originating in
% the module's own .erl file. epp inserts `{attribute, _, file, {File, _}}`
% markers at include boundaries; we track the current file and keep matching
% forms (and drop the markers themselves).
-spec own_forms(file:filename(), [ast_erl:form()]) -> [ast_erl:form()].
own_forms(File, Forms) ->
    Base = filename:basename(File),
    {Kept, _} = lists:foldl(
        fun({attribute, _, file, {F, _}}, {Acc, _Cur}) ->
                {Acc, filename:basename(F)};
           (Form, {Acc, Cur}) when Cur =:= Base ->
                {[Form | Acc], Cur};
           (_Form, {Acc, Cur}) ->
                {Acc, Cur}
        end, {[], Base}, Forms),
    lists:reverse(Kept).

% Collectors over the raw Erlang AST. Each returns a (possibly nested) map that
% is deep-merged into the module report.
-spec raw_collectors([ast_erl:form()]) -> [report()].
raw_collectors(RawForms) ->
    [collect_corpus(RawForms),
     collect_spec_coverage(RawForms),
     collect_features(RawForms)].

% Collectors over the transformed (internal) AST.
-spec tx_collectors([ast:form()]) -> [report()].
tx_collectors(_TxForms) ->
    [].

-spec try_transform(file:filename(), [ast_erl:form()]) -> {ok, [ast:form()]} | error.
try_transform(File, RawForms) ->
    try {ok, ast_transform:trans(File, RawForms)}
    catch
        %% Expected: undefined names, unsupported constructs, etc.
        throw:{etylizer, _Kind, _Msg} -> error;
        %% Unexpected: keep sweeping the remaining modules.
        Class:Reason:Stack ->
            ?LOG_WARN("ast_transform crashed on ~s: ~p:~p~n~p", [File, Class, Reason, Stack]),
            error
    end.

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
%% #2 spec coverage + type-feature counts (raw AST)
%%
%% Matches the reference escripts count_specs.escript (coverage) and
%% count_unions.escript (feature counts). `utils:everything/2' is identical to
%% the escripts' own generic traversal, so the counts coincide (up to the
%% stricter etylizer parser, which drops files with unresolved includes/macros).
%% ---------------------------------------------------------------------------

% Spec coverage: functions carrying a matching -spec vs. not (count_specs).
-spec collect_spec_coverage([ast_erl:form()]) -> report().
collect_spec_coverage(RawForms) ->
    Funs = sets:from_list(utils:everything(
        fun({function, _, Name, Arity, _}) -> {ok, {Name, Arity}};
           (_) -> error
        end, RawForms)),
    SpecTargets = sets:from_list(utils:everything(
        fun({attribute, _, spec, {{Name, Arity}, _}}) when is_atom(Name) -> {ok, {Name, Arity}};
           ({attribute, _, spec, {{_Mod, Name, Arity}, _}}) -> {ok, {Name, Arity}};
           (_) -> error
        end, RawForms)),
    NSpecced = sets:size(sets:intersection(Funs, SpecTargets)),
    NUnspecced = sets:size(Funs) - NSpecced,
    #{corpus => #{n_specced => NSpecced, n_unspecced => NUnspecced}}.

% Type-system feature counts over specs and type declarations (count_unions).
% `dynamic()' indirect (a user type expanding to dynamic) needs the symtab and
% is added with the call-classification collector.
-spec collect_features([ast_erl:form()]) -> report().
collect_features(RawForms) ->
    SpecClauses = spec_type_clauses(RawForms),
    Union = length(utils:everything(
        fun({type, _, union, _}) -> {rec, u}; (_) -> error end, RawForms)),
    DynamicDirect = length(utils:everything(
        fun({type, _, dynamic, []}) -> {ok, d}; (_) -> error end, RawForms)),
    Overloaded = length([1 || Types <- SpecClauses, length(Types) > 1]),
    Polymorphic = length([1 || Types <- SpecClauses, is_polymorphic(Types)]),
    Numeric = length([1 || Types <- SpecClauses, has_numeric_type(Types)]),
    #{features => #{
        union => Union,
        overloaded => Overloaded,
        polymorphic => Polymorphic,
        numeric => Numeric,
        dynamic_direct => DynamicDirect
    }}.

% The type-clause lists of each unqualified -spec (count_unions considers only
% unqualified specs for the per-spec feature counts).
-spec spec_type_clauses([ast_erl:form()]) -> [[ast_erl:ty()]].
spec_type_clauses(RawForms) ->
    utils:everything(
        fun({attribute, _, spec, {{Name, _Arity}, Types}}) when is_atom(Name) -> {ok, Types};
           (_) -> error
        end, RawForms).

% A spec is polymorphic if some clause reuses a type variable within the
% function type (ignoring `when' constraints) — count_unions's definition.
-spec is_polymorphic([ast_erl:ty()]) -> boolean().
is_polymorphic(TypeClauses) ->
    lists:any(fun is_clause_polymorphic/1, TypeClauses).

-spec is_clause_polymorphic(ast_erl:ty()) -> boolean().
is_clause_polymorphic({type, _, bounded_fun, [FunType, _Constraints]}) ->
    has_repeated_var(FunType);
is_clause_polymorphic(FunType) ->
    has_repeated_var(FunType).

-spec has_repeated_var(term()) -> boolean().
has_repeated_var(FunType) ->
    Vars = utils:everything(
        fun({var, _, '_'}) -> error;
           ({var, _, Name}) -> {ok, Name};
           (_) -> error
        end, FunType),
    length(Vars) =/= length(lists:usort(Vars)).

-spec has_numeric_type([ast_erl:ty()]) -> boolean().
has_numeric_type(Types) ->
    [] =/= utils:everything(
        fun(T) -> case is_numeric_type(T) of true -> {ok, T}; false -> error end end,
        Types).

-spec is_numeric_type(term()) -> boolean().
is_numeric_type({type, _, Name, []}) ->
    lists:member(Name, [integer, non_neg_integer, pos_integer, neg_integer,
                        byte, char, arity]);
is_numeric_type({type, _, range, _}) -> true;
is_numeric_type({integer, _, _}) -> true;
is_numeric_type(_) -> false.

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
