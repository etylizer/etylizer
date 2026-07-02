-module(count_features).

% @doc Counts type system feature usage in a codebase.
% Uses the full etylizer pipeline (parse + AST transform) to count features
% on the transformed internal AST.

-export([main/1]).

-include("log.hrl").
-include("parse.hrl").
-include("etylizer_main.hrl").

-spec main([string()]) -> ok.
main(Args) ->
    case parse_args(Args) of
        {error, Msg} ->
            io:format("~s~n", [Msg]),
            io:format("Usage: count_features [-I <include_dir>]... <file_or_dir>...~n");
        {ok, Includes, Paths} ->
            Files = lists:flatmap(fun collect_erl_files/1, Paths),
            Opts = #opts{includes = Includes, no_deps = true},
            log:init(warn),
            global_state:with_new_state(fun() ->
                parse_cache:init(Opts),
                stdtypes:init(),
                try
                    AllForms = lists:flatmap(fun(F) -> parse_file(F) end, Files),
                    count_and_report(AllForms, length(Files))
                after
                    parse_cache:cleanup(),
                    stdtypes:cleanup()
                end
            end)
    end.

-spec parse_args([string()]) -> {ok, [string()], [string()]} | {error, string()}.
parse_args(Args) -> parse_args(Args, [], []).

-spec parse_args([string()], [string()], [string()]) ->
    {ok, [string()], [string()]} | {error, string()}.
parse_args([], _Includes, []) -> {error, "No files or directories given"};
parse_args([], Includes, Paths) -> {ok, Includes, Paths};
parse_args(["-I", Dir | Rest], Includes, Paths) ->
    parse_args(Rest, Includes ++ [Dir], Paths);
parse_args(["-I" | _], _, _) -> {error, "-I requires an argument"};
parse_args([Path | Rest], Includes, Paths) ->
    parse_args(Rest, Includes, Paths ++ [Path]).

-spec collect_erl_files(string()) -> [string()].
collect_erl_files(Path) ->
    case filelib:is_dir(Path) of
        true -> filelib:fold_files(Path, "\\.erl$", true, fun(F, Acc) -> [F | Acc] end, []);
        false -> [Path]
    end.

-spec parse_file(string()) -> [ast:form()].
parse_file(File) ->
    try parse_cache:parse(intern, File)
    catch _:_ ->
        io:format(standard_error, "Warning: failed to parse ~s, skipping~n", [File]),
        []
    end.

-spec count_and_report([ast:form()], non_neg_integer()) -> ok.
count_and_report(AllForms, NFiles) ->
    %% Extract function declarations
    FunDecls = everything(
        fun({function, _, _, _, _} = F) -> {ok, F}; (_) -> error end,
        AllForms),

    %% Count case expressions in transformed AST (including nested)
    Cases = length(everything(
        fun({'case', _, _, _}) -> {rec, c}; (_) -> error end,
        FunDecls)),

    %% Count modules: {attribute, loc(), module, ModName}
    Modules = length(everything(
        fun({attribute, _, module, _}) -> {ok, m}; (_) -> error end,
        AllForms)),

    %% Count specs: {attribute, loc(), spec|callback, Name, Arity, TyScheme, _}
    Specs = length(everything(
        fun({attribute, _, spec, _, _, _, _}) -> {ok, s}; (_) -> error end,
        AllForms)),

    io:format("Case expressions:      ~b~n", [Cases]),
    io:format("Function declarations:  ~b~n", [length(FunDecls)]),
    io:format("(~b files scanned, ~b modules, ~b specs total)~n",
              [NFiles, Modules, Specs]),
    ok.

%% {ok, X}  — collect X, stop recursing into this term
%% {rec, X} — collect X, keep recursing into children
%% error    — don't collect, recurse into children
-spec everything(fun((term()) -> {ok, T} | {rec, T} | error), term()) -> [T].
everything(F, T) ->
    Recurse = fun() ->
        case T of
            X when is_list(X) -> lists:flatmap(fun(E) -> everything(F, E) end, X);
            X when is_tuple(X) -> lists:flatmap(fun(E) -> everything(F, E) end, tuple_to_list(X));
            X when is_map(X) -> lists:flatmap(fun(E) -> everything(F, E) end, maps:to_list(X));
            _ -> []
        end
    end,
    case F(T) of
        error -> Recurse();
        {ok, X} -> [X];
        {rec, X} -> [X | Recurse()]
    end.
