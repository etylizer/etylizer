-module(diagnostics).

% @doc Structured, machine-readable type-check diagnostics.
%
% etylizer historically either throws on the first error (early-exit) or prints a
% per-function text report. This module provides a data representation of a diagnostic
% plus a JSON encoder, so an external tool (e.g. the ELP language server) can run
% etylizer as a subprocess and turn each diagnostic into an editor marker.

-export([
    from_error/5,
    kind_to_severity/1,
    loc_from_message/2,
    filter_by_file/2,
    to_json_iolist/1,
    results_to_json_iolist/2,
    error_to_json_iolist/2
]).

-export_type([diagnostic/0, severity/0, diag_kind/0]).

-type severity() :: error | warning.

% The coarse error kind as thrown via {etylizer, Kind, Msg}. The fine-grained
% distinction (tyerror vs redundant_branch vs non_exhaustive_case) is currently only
% present in the human-readable message.
-type diag_kind() :: ty_error | name_error | parse_error | unsupported
                   | not_implemented | bug | other.

-type diagnostic() ::
    #{ kind := diag_kind(),
       loc := ast:loc(),
       message := string(),
       function := atom() | undefined,
       arity := arity() | undefined,
       severity := severity() }.

-spec kind_to_severity(diag_kind()) -> severity().
kind_to_severity(_Kind) -> error.

-spec from_error(diag_kind(), ast:loc(), string(), atom() | undefined, arity() | undefined)
    -> diagnostic().
from_error(Kind, Loc, Message, Function, Arity) ->
    #{ kind => Kind,
       loc => Loc,
       message => Message,
       function => Function,
       arity => Arity,
       severity => kind_to_severity(Kind) }.

% Located errors are formatted by errors:generic_error/5 as "<File>:<Line>:<Col>: ...".
% This recovers the precise {loc, File, Line, Col} from such a message so the diagnostic
% points at the offending expression rather than the function declaration. Falls back to
% the given location (e.g. the function declaration) for messages without a parseable
% location prefix for that file.
-spec loc_from_message(string(), ast:loc()) -> ast:loc().
loc_from_message(Msg, {loc, File, _, _} = Fallback) when is_list(Msg) ->
    Prefix = File ++ ":",
    case lists:prefix(Prefix, Msg) of
        true ->
            case parse_line_col(lists:nthtail(length(Prefix), Msg)) of
                {Line, Col} -> {loc, File, Line, Col};
                error -> Fallback
            end;
        false -> Fallback
    end;
loc_from_message(_Msg, Fallback) -> Fallback.

-spec parse_line_col(string()) -> {integer(), integer()} | error.
parse_line_col(S) ->
    case take_int(S) of
        {Line, [$: | S1]} ->
            case take_int(S1) of
                {Col, [$: | _]} -> {Line, Col};
                _ -> error
            end;
        _ -> error
    end.

-spec take_int(string()) -> {integer(), string()} | error.
take_int(S) ->
    case lists:splitwith(fun(C) -> C >= $0 andalso C =< $9 end, S) of
        {[], _} -> error;
        {Digits, Rest} -> {list_to_integer(Digits), Rest}
    end.

% Keep only diagnostics whose location file is one of the given files (normalized).
% An empty file list means "keep everything". Synthetic "AUTO" locations are dropped.
-spec filter_by_file([diagnostic()], [file:filename()]) -> [diagnostic()].
filter_by_file(Diags, []) -> [D || D <- Diags, has_real_loc(D)];
filter_by_file(Diags, Files) ->
    Norm = sets:from_list([utils:normalize_path(F) || F <- Files]),
    [D || D <- Diags,
          has_real_loc(D),
          sets:is_element(utils:normalize_path(loc_file(D)), Norm)].

-spec has_real_loc(diagnostic()) -> boolean().
has_real_loc(#{loc := {loc, "AUTO", _, _}}) -> false;
has_real_loc(_) -> true.

-spec loc_file(diagnostic()) -> file:filename().
loc_file(#{loc := {loc, File, _, _}}) -> File.

% Encodes a list of diagnostics as a JSON array (one object per diagnostic).
% Diagnostics with a synthetic "AUTO" location are dropped (they have no source span).
-spec to_json_iolist([diagnostic()]) -> iolist().
to_json_iolist(Diags) ->
    Objs = [diag_to_json(D) || D <- Diags, has_real_loc(D)],
    json:encode(Objs).

-spec diag_to_json(diagnostic()) -> map().
diag_to_json(#{kind := Kind, loc := {loc, File, Line, Col}, message := Msg,
               function := Fun, arity := Arity, severity := Sev}) ->
    #{ <<"file">> => to_bin(File),
       <<"line">> => num_or_null(Line),
       <<"column">> => num_or_null(Col),
       <<"kind">> => atom_to_binary(Kind, utf8),
       <<"severity">> => atom_to_binary(Sev, utf8),
       <<"message">> => to_bin(Msg),
       <<"function">> => atom_or_null(Fun),
       <<"arity">> => num_or_null(Arity) }.

% Encodes a tool-level failure (e.g. a parse error of the input file or an internal bug)
% as a single JSON object, to be written to stderr alongside a non-zero exit code.
% Encodes a full json-mode result: which source files were (re)checked this run, and the
% diagnostics found. A language server replaces its cached diagnostics for a file only when
% that file appears in "checked" (etylizer's per-function incremental check re-checks every
% currently-failing function, so the diagnostics for a checked file are complete), and keeps
% its cache for files not in "checked" (skipped because unchanged).
-spec results_to_json_iolist([file:filename()], [diagnostic()]) -> iolist().
results_to_json_iolist(CheckedFiles, Diags) ->
    Objs = [diag_to_json(D) || D <- Diags, has_real_loc(D)],
    json:encode(#{ <<"checked">> => [to_bin(F) || F <- CheckedFiles],
                   <<"diagnostics">> => Objs }).

-spec error_to_json_iolist(atom(), string()) -> iolist().
error_to_json_iolist(Kind, Msg) ->
    json:encode(#{ <<"error">> => to_bin(Msg),
                   <<"kind">> => atom_to_binary(Kind, utf8) }).

-spec num_or_null(integer() | undefined) -> integer() | null.
num_or_null(N) when is_integer(N), N >= 0 -> N;
num_or_null(_) -> null.

-spec atom_or_null(atom()) -> binary() | null.
atom_or_null(undefined) -> null;
atom_or_null(A) when is_atom(A) -> atom_to_binary(A, utf8).

-spec to_bin(iodata()) -> binary().
to_bin(B) when is_binary(B) -> B;
to_bin(S) ->
    case unicode:characters_to_binary(S) of
        Bin when is_binary(Bin) -> Bin;
        _ -> list_to_binary(io_lib:format("~tp", [S]))
    end.
