-module(errors).

-export([
    unsupported/3, unsupported/2,
    name_error/3, 
    name_error_no_loc/2,
    uncovered_case/3, uncovered_case/4, bug/2, bug/1,
    ty_error/2, ty_error/3, ty_error/1, not_implemented/1, parse_error/1, some_error/2,
    caught/2
]).

-export_type([kind/0]).

-include("etylizer.hrl").

% The functions of this module throw {etylizer, kind(), string()}.
-type kind() :: error | unsupported | name_error | bug | ty_error | not_implemented | parse_error.

% The kind and the message of a caught {etylizer, Kind, Msg}. An exception carries no type: a
% catch clause sees the parts of its value as term().
-spec caught(term(), term()) -> {kind(), string()}.
caught(Kind, Msg) -> {?assert_type(Kind, kind()), ?assert_type(Msg, string())}.

-spec generic_error(kind(), string()) -> no_return().
generic_error(Kind, Msg) -> throw({etylizer, Kind, Msg}).

-spec generic_error(kind(), ast:loc(), string(), string(), any()) -> no_return().
generic_error(Kind, Loc, Prefix, Msg, Args) ->
    generic_error(Kind,
                  utils:sformat("~s: ~s: ~s",
                                ast:format_loc(Loc), Prefix, utils:sformat(Msg, Args))).

-spec some_error(string(), any()) -> no_return().
some_error(Msg, Args) ->
    generic_error(error, utils:sformat(Msg, Args)).

-spec unsupported(ast:loc(), string(), any()) -> no_return().
unsupported(Loc, Msg, Args) ->
    generic_error(unsupported, Loc, "Unsupported language feature", Msg, Args).

-spec unsupported(ast:loc(), string()) -> no_return().
unsupported(Loc, Msg) -> unsupported(Loc, Msg, []).

-spec name_error(ast:loc(), string(), any()) -> no_return().
name_error(Loc, Msg, Args) ->
    generic_error(name_error, Loc, "Name error", Msg, Args).

-spec name_error_no_loc(string(), any()) -> no_return().
name_error_no_loc(Msg, Args) ->
    generic_error(name_error, utils:sformat("Name error: ~s", utils:sformat(Msg, Args))).

-spec bug(string()) -> no_return().
bug(Msg) ->
    throw({etylizer, bug, "BUG: " ++ Msg}).

-spec bug(string(), any()) -> no_return().
bug(Msg, Args) ->
    throw({etylizer, bug, utils:sformat("BUG: " ++ Msg, Args)}).

-spec uncovered_case(file:filename(), t:lineno(), any()) -> no_return().
uncovered_case(File, Line, X) ->
    bug("uncovered case in ~s:~w, unmatched value: ~w", [File, Line, X]).

-spec uncovered_case(file:filename(), t:lineno(), string(), any()) -> no_return().
uncovered_case(File, Line, InputFile, X) ->
    bug("uncovered case in ~s:~w, input file ~s, unmatched value: ~w", [File, Line, InputFile, X]).

-spec ty_error(ast:loc(), string(), any()) -> no_return().
ty_error(Loc, Msg, Args) ->
    generic_error(ty_error, Loc, "Type error", Msg, Args).

-spec ty_error(ast:loc(), string()) -> no_return().
ty_error(X, Msg) -> ty_error(X, Msg, []).

-spec ty_error(string()) -> no_return().
ty_error(Msg) -> generic_error(ty_error, Msg).

-spec not_implemented(string()) -> no_return().
not_implemented(Msg) -> throw({etylizer, not_implemented, Msg}).

-spec parse_error(string()) -> no_return().
parse_error(Msg) -> generic_error(parse_error, Msg).
