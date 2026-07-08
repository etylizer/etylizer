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
            OwnFunKeys = sets:from_list([{N, A} || {function, _, N, A, _} <- OwnRaw]),
            RawReport = lists:foldl(fun deep_merge/2, Base#{parse => ok},
                                    raw_collectors(OwnRaw)),
            case try_transform(File, RawForms) of
                {ok, TxForms} ->
                    OwnTxFuns = [F || F = {function, _, N, A, _} <- TxForms,
                                      sets:is_element({N, A}, OwnFunKeys)],
                    lists:foldl(fun deep_merge/2, RawReport, tx_collectors(OwnTxFuns));
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
     collect_features(RawForms),
     collect_if_case(RawForms),
     collect_index_calls(RawForms)].

% Collectors over the transformed (internal) AST, restricted to the module's
% own function declarations.
-spec tx_collectors([ast:fun_decl()]) -> [report()].
tx_collectors(TxFuns) ->
    [collect_patterns(TxFuns)].

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
%% #5 if-vs-case, with final-clause classification of each `if' (raw AST)
%%
%% Must run on the raw AST: after the ast_transform refactor, `if' becomes
%% `case' in the transformed AST, so `if' is only visible here. Matches
%% count_if_case.escript.
%% ---------------------------------------------------------------------------
-spec collect_if_case([ast_erl:form()]) -> report().
collect_if_case(RawForms) ->
    FunClauseLists = [Cls || {function, _, _, _, Cls} <- RawForms],
    Cases = length(utils:everything(
        fun({'case', _, _, _}) -> {rec, c}; (_) -> error end, RawForms)),
    Receives = length(utils:everything(
        fun({'receive', _, _}) -> {rec, r};
           ({'receive', _, _, _, _}) -> {rec, r};
           (_) -> error
        end, RawForms)),
    IfClausesList = utils:everything(
        fun({'if', _, Clauses}) -> {rec, Clauses}; (_) -> error end, RawForms),
    Classes = [classify_if_last_guard(Cs) || Cs <- IfClausesList],
    #{if_case => #{
        funs => length(FunClauseLists),
        multi_clause_funs => length([1 || Cls <- FunClauseLists, length(Cls) > 1]),
        cases => Cases,
        receives => Receives,
        ifs => length(IfClausesList),
        if_true_last => count_eq(true_catch_all, Classes),
        if_cmp_last => count_eq(comparison, Classes),
        if_other_last => count_eq(other, Classes)
    }}.

-spec count_eq(term(), [term()]) -> non_neg_integer().
count_eq(X, Xs) -> length([1 || Y <- Xs, Y =:= X]).

% Classify an `if' by the guard of its final clause: `true' catch-all, a
% (conjunction/disjunction of) comparison operators, or anything else.
-spec classify_if_last_guard([ast_erl:if_clause()]) -> true_catch_all | comparison | other.
classify_if_last_guard([]) -> other;
classify_if_last_guard(Clauses) ->
    case lists:last(Clauses) of
        {clause, _, _, Guards, _} -> classify_guard(Guards);
        _ -> other
    end.

% Guards :: [[guard_test()]] -- outer list is `;' (disjunction), inner is `,'.
-spec classify_guard([[ast_erl:guard_test()]]) -> true_catch_all | comparison | other.
classify_guard([]) -> other;
classify_guard(Disjuncts) ->
    IsTrueDisjunct = fun([{atom, _, true}]) -> true; (_) -> false end,
    case lists:any(IsTrueDisjunct, Disjuncts) of
        true -> true_catch_all;
        false ->
            case lists:all(fun(D) -> lists:all(fun is_comparison/1, D) end, Disjuncts) of
                true -> comparison;
                false -> other
            end
    end.

-spec is_comparison(ast_erl:guard_test()) -> boolean().
is_comparison({op, _, Op, _, _}) ->
    lists:member(Op, ['<', '=<', '>', '>=', '==', '/=', '=:=', '=/=']);
is_comparison(_) -> false.

%% ---------------------------------------------------------------------------
%% #4 index arguments of element/setelement/lists:key* (raw AST)
%%
%% element/setelement (remote or local) match s.escript exactly (index = arg 1).
%% lists:key*/ukey* use a callee->index-position table (the index tuple field is
%% not always arg 1) and are reported separately so element/setelement stays
%% comparable to the published number. An index argument is `literal' iff it is
%% an integer literal, else `non_literal'.
%% ---------------------------------------------------------------------------
-spec collect_index_calls([ast_erl:form()]) -> report().
collect_index_calls(RawForms) ->
    Tagged = utils:everything(fun index_call_arg/1, RawForms),
    {EsL, EsNL} = tally_literal([Arg || {element_setelement, Arg} <- Tagged]),
    {LkL, LkNL} = tally_literal([Arg || {lists_key, Arg} <- Tagged]),
    #{index_calls => #{
        literal => EsL + LkL,
        non_literal => EsNL + LkNL,
        element_setelement => #{literal => EsL, non_literal => EsNL},
        lists_key => #{literal => LkL, non_literal => LkNL}
    }}.

-spec index_call_arg(term()) -> {ok, {atom(), ast_erl:exp()}} | error.
index_call_arg({call, _, {remote, _, {atom, _, erlang}, {atom, _, element}}, [A1, _]}) ->
    {ok, {element_setelement, A1}};
index_call_arg({call, _, {atom, _, element}, [A1, _]}) ->
    {ok, {element_setelement, A1}};
index_call_arg({call, _, {remote, _, {atom, _, erlang}, {atom, _, setelement}}, [A1, _, _]}) ->
    {ok, {element_setelement, A1}};
index_call_arg({call, _, {atom, _, setelement}, [A1, _, _]}) ->
    {ok, {element_setelement, A1}};
index_call_arg({call, _, {remote, _, {atom, _, lists}, {atom, _, Fun}}, Args}) ->
    case lists_key_index_pos(Fun, length(Args)) of
        {ok, Pos} -> {ok, {lists_key, lists:nth(Pos, Args)}};
        error -> error
    end;
index_call_arg(_) -> error.

-spec tally_literal([ast_erl:exp()]) -> {non_neg_integer(), non_neg_integer()}.
tally_literal(Args) ->
    lists:foldl(
      fun({integer, _, _}, {L, NL}) -> {L + 1, NL};
         (_, {L, NL}) -> {L, NL + 1}
      end, {0, 0}, Args).

% Argument position (1-based) of the tuple-index in a lists:key*/ukey* call.
-spec lists_key_index_pos(atom(), arity()) -> {ok, pos_integer()} | error.
lists_key_index_pos(keyfind, 3) -> {ok, 2};
lists_key_index_pos(keysearch, 3) -> {ok, 2};
lists_key_index_pos(keymember, 3) -> {ok, 2};
lists_key_index_pos(keytake, 3) -> {ok, 2};
lists_key_index_pos(keydelete, 3) -> {ok, 2};
lists_key_index_pos(keyreplace, 4) -> {ok, 2};
lists_key_index_pos(keystore, 4) -> {ok, 2};
lists_key_index_pos(keymap, 3) -> {ok, 2};
lists_key_index_pos(keysort, 2) -> {ok, 1};
lists_key_index_pos(ukeysort, 2) -> {ok, 1};
lists_key_index_pos(keymerge, 3) -> {ok, 1};
lists_key_index_pos(ukeymerge, 3) -> {ok, 1};
lists_key_index_pos(_, _) -> error.

%% ---------------------------------------------------------------------------
%% #3 pattern matches, branches, and type tests in guards (transformed AST)
%%
%% Runs on the transformed AST, where `if' and multi-clause heads are `case's,
%% so all dispatch is uniform. Type tests are `erlang:is_X/1' calls in guards;
%% "on var" is a test of a variable, "on bound var" is a test of a variable that
%% the enclosing clause's pattern binds — decided via etylizer's own
%% local_bind/local_ref annotations (no external binding analysis needed).
%% Matches the erlang-2026 pattern-type-tests table.
%% ---------------------------------------------------------------------------
-spec collect_patterns([ast:fun_decl()]) -> report().
collect_patterns(TxFuns) ->
    PatMatches = length(utils:everything(
        fun({'case', _, _, _}) -> {rec, x};
           ({'receive', _, _}) -> {rec, x};
           ({receive_after, _, _, _, _}) -> {rec, x};
           ({'try', _, _, _, _, _}) -> {rec, x};
           (_) -> error
        end, TxFuns)),
    Branches = length(utils:everything(
        fun({case_clause, _, _, _, _}) -> {rec, x};
           ({catch_clause, _, _, _, _, _, _}) -> {rec, x};
           (_) -> error
        end, TxFuns)),
    ClauseCtxs = utils:everything(
        fun({case_clause, _, Pat, Guards, _}) -> {rec, {pat_bound_tokens(Pat), Guards}};
           ({fun_clause, _, Pats, Guards, _}) -> {rec, {pat_bound_tokens(Pats), Guards}};
           ({catch_clause, _, X, P, S, Guards, _}) -> {rec, {pat_bound_tokens([X, P, S]), Guards}};
           (_) -> error
        end, TxFuns),
    {TT, TTVar, TTBound} = lists:foldl(fun tally_type_tests/2, {0, 0, 0}, ClauseCtxs),
    #{patterns => #{
        pat_matches => PatMatches,
        branches => Branches,
        type_tests => TT,
        tt_var => TTVar,
        tt_bound => TTBound
    }}.

% The variable tokens a pattern binds/mentions (both fresh binds and, for
% non-linear patterns, references).
-spec pat_bound_tokens(term()) -> sets:set(ast:local_varname()).
pat_bound_tokens(Pat) ->
    sets:from_list(utils:everything(
        fun({var, _, {local_bind, T}}) -> {ok, T};
           ({var, _, {local_ref, T}}) -> {ok, T};
           (_) -> error
        end, Pat)).

-spec tally_type_tests({sets:set(ast:local_varname()), [ast:guard()]},
                       {integer(), integer(), integer()}) ->
          {integer(), integer(), integer()}.
tally_type_tests({BoundSet, Guards}, {TT, TTVar, TTBound}) ->
    TestArgs = utils:everything(fun type_test_call/1, Guards),
    lists:foldl(
      fun(Arg, {T, V, B}) ->
          case Arg of
              {var, _, {Ref, Token}} when Ref =:= local_ref; Ref =:= local_bind ->
                  B1 = case sets:is_element(Token, BoundSet) of true -> B + 1; false -> B end,
                  {T + 1, V + 1, B1};
              _ ->
                  {T + 1, V, B}
          end
      end, {TT, TTVar, TTBound}, TestArgs).

% A guard `is_X(Arg)' type-test call (single argument); yields its argument.
-spec type_test_call(term()) -> {ok, ast:exp()} | error.
type_test_call({call, _, {var, _, {qref, erlang, Name, 1}}, [Arg]}) ->
    case is_type_test_name(Name) of true -> {ok, Arg}; false -> error end;
type_test_call({call, _, {var, _, {ref, Name, 1}}, [Arg]}) ->
    case is_type_test_name(Name) of true -> {ok, Arg}; false -> error end;
type_test_call(_) -> error.

-spec is_type_test_name(atom()) -> boolean().
is_type_test_name(Name) ->
    lists:member(Name, [is_atom, is_binary, is_bitstring, is_boolean, is_float,
                        is_function, is_integer, is_list, is_map, is_number,
                        is_pid, is_port, is_reference, is_tuple]).

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
