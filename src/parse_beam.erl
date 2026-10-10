-module(parse_beam).

% @doc This module extracts Erlang abstract forms from compiled BEAM files.
% This enables etylizer to typecheck Elixir projects by reading their compiled
% BEAM output, which contains standard Erlang abstract forms in the debug_info chunk.

-export([parse_beam_file/1, source_path/2]).

-include("log.hrl").

-spec parse_beam_file(file:filename()) -> {ok, [ast_erl:form()]} | error.
parse_beam_file(Path) ->
    case beam_lib:chunks(Path, [debug_info]) of
        {ok, {Module, [{debug_info, {debug_info_v1, Backend, Data}}]}} ->
            extract_forms(Path, Module, Backend, Data);
        {ok, {_Module, [{debug_info, no_debug_info}]}} ->
            ?LOG_ERROR("No debug_info in BEAM file ~s. Compile with debug_info enabled.", Path),
            error;
        {error, beam_lib, Reason} ->
            ?LOG_ERROR("Failed to read BEAM file ~s: ~p", Path, Reason),
            error
    end.

-spec extract_forms(file:filename(), module(), module(), term()) ->
    {ok, [ast_erl:form()]} | error.
extract_forms(Path, Module, Backend, Data) ->
    case Backend:debug_info(erlang_v1, Module, Data, []) of
        {ok, Forms0} ->
            Forms1 = filter_elixir_generated(Forms0),
            Forms2 = synthesize_default_arg_specs(Forms1),
            {ok, Forms2};
        {error, Reason} ->
            ?LOG_ERROR("Failed to extract forms from ~s: ~p", Path, Reason),
            error
    end.

% Resolve the original source file (.ex/.erl) a BEAM was compiled from, used
% only to make error locations point at readable source. The forms carry
% {attribute, _, file, {SourcePath, _}} from compilation; that path may be
% absolute, or relative to the project root (in which case we search upward from
% the BEAM file's directory). Falls back to BeamPath if it cannot be located.
-spec source_path(file:filename(), [ast_erl:form()]) -> file:filename().
source_path(BeamPath, Forms) ->
    case lists:keyfind(file, 3, Forms) of
        {attribute, _, file, {SrcPath, _}} ->
            case filelib:is_file(SrcPath) of
                true -> SrcPath;
                false ->
                    BeamDir = filename:dirname(BeamPath),
                    case find_source_upward(BeamDir, SrcPath) of
                        {ok, Resolved} -> Resolved;
                        error -> BeamPath
                    end
            end;
        false ->
            BeamPath
    end.

-spec find_source_upward(file:filename(), file:filename()) -> {ok, file:filename()} | error.
find_source_upward(Dir, RelPath) ->
    Candidate = filename:join(Dir, RelPath),
    case filelib:is_file(Candidate) of
        true -> {ok, Candidate};
        false ->
            Parent = filename:dirname(Dir),
            case Parent =:= Dir of
                true -> error;  % reached filesystem root
                false -> find_source_upward(Parent, RelPath)
            end
    end.

% Filter out Elixir auto-generated functions that have no spec (e.g. __info__/1).
-spec filter_elixir_generated([ast_erl:form()]) -> [ast_erl:form()].
filter_elixir_generated(Forms) ->
    lists:filter(fun(Form) ->
        case Form of
            {function, _, '__info__', 1, _} -> false;
            _ -> true
        end
    end, Forms).

% Synthesize specs for Elixir default-argument wrapper functions.
% When Elixir has `@spec foo(a, b, c) :: d` with `\\ default` on parameter c,
% it generates foo/2 that calls foo/3 with the default value. foo/2 has no spec.
% We detect this pattern and derive foo/2's spec by dropping the last parameter.
-spec synthesize_default_arg_specs([ast_erl:form()]) -> [ast_erl:form()].
synthesize_default_arg_specs(Forms) ->
    Exports = lists:usort([{N,A} || {attribute, _, export, Es} <- Forms, {N,A} <- Es]),
    Specs = maps:from_list([{{N,A}, S} || {attribute, _, spec, {{N,A}, S}} <- Forms]),
    Funs = maps:from_list([{{N,A}, Clauses} || {function, _, N, A, Clauses} <- Forms]),
    NewSpecs = lists:filtermap(
        fun({Name, Arity}) ->
            case maps:is_key({Name, Arity}, Specs) of
                true -> false;  % already has a spec
                false ->
                    case is_default_arg_wrapper(Name, Arity, Funs) of
                        {true, HigherArity} ->
                            case maps:find({Name, HigherArity}, Specs) of
                                {ok, SpecClauses} ->
                                    case derive_lower_arity_spec(Name, Arity, SpecClauses) of
                                        {ok, NewSpec} ->
                                            ?LOG_DEBUG("Synthesized spec for ~p/~p from ~p/~p",
                                                Name, Arity, Name, HigherArity),
                                            {true, NewSpec};
                                        error -> false
                                    end;
                                error -> false
                            end;
                        false -> false
                    end
            end
        end, Exports),
    Forms ++ NewSpecs.

% Check if a function is a default-argument wrapper: single clause that calls
% the same function with more arguments (forwarding all params plus literals).
-spec is_default_arg_wrapper(atom(), arity(), map()) -> {true, arity()} | false.
is_default_arg_wrapper(Name, Arity, Funs) ->
    case maps:find({Name, Arity}, Funs) of
        {ok, [{clause, _, Params, [], [{call, _, {atom, _, Name}, CallArgs}]}]} ->
            CallArity = length(CallArgs),
            case CallArity > Arity andalso length(Params) =:= Arity of
                true -> {true, CallArity};
                false -> false
            end;
        _ -> false
    end.

% Derive a spec for a lower arity by dropping trailing parameters from a higher-arity spec.
-spec derive_lower_arity_spec(atom(), arity(), [tuple()]) -> {ok, ast_erl:form()} | error.
derive_lower_arity_spec(Name, TargetArity, SpecClauses) ->
    NewClauses = lists:filtermap(
        fun(Clause) ->
            case Clause of
                {type, Loc, 'fun', [{type, PLoc, product, Params}, RetType]} ->
                    case length(Params) > TargetArity of
                        true ->
                            TrimmedParams = lists:sublist(Params, TargetArity),
                            {true, {type, Loc, 'fun',
                                [{type, PLoc, product, TrimmedParams}, RetType]}};
                        false -> false
                    end;
                _ -> false
            end
        end, SpecClauses),
    case NewClauses of
        [] -> error;
        _ -> {ok, {attribute, 0, spec, {{Name, TargetArity}, NewClauses}}}
    end.
