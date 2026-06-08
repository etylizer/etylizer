-module(parse_beam).

% extracts Erlang abstract forms from compiled BEAM files

-export([parse_beam_file/1]).

-include("log.hrl").

% beam_lib reads the forms with the backend named in the debug_info chunk
-spec parse_beam_file(file:filename()) -> {ok, [ast_erl:form()]} | error.
parse_beam_file(Path) ->
    case beam_lib:chunks(Path, [abstract_code]) of
        {ok, {_, [{abstract_code, {raw_abstract_v1, Forms}}]}} ->
            {ok, Forms};
        {ok, {_, [{abstract_code, no_abstract_code}]}} ->
            ?LOG_ERROR("No debug_info in BEAM file ~s. Compile with debug_info enabled.", Path),
            error;
        {error, beam_lib, {missing_backend, _, Backend}} ->
            ?LOG_ERROR("The debug_info of ~s is read with module ~w, which is not on the code path. "
                "Add its directory with --pa.", Path, Backend),
            error;
        {error, beam_lib, Reason} ->
            ?LOG_ERROR("Failed to read BEAM file ~s: ~p", Path, Reason),
            error
    end.
