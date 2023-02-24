-module(errors).

-export([
    unsupported/3, unsupported/2,
    name_error/3, name_error/2,
    uncovered_case/3, bug/2, bug/1,
    ty_error/2, ty_error/3, not_implemented/1
]).

-spec generic_error(atom(), ast:loc(), string(), string(), any()) -> no_return().
generic_error(Kind, Loc, Prefix, Msg, Args) ->
    halt(3).

-spec unsupported(ast:loc(), string(), any()) -> no_return().
unsupported(Loc, Msg, Args) ->
    halt(5).

-spec unsupported(ast:loc(), string()) -> no_return().
unsupported(Loc, Msg) -> unsupported(Loc, Msg, []).

-spec name_error(ast:loc(), string(), any()) -> no_return().
name_error(Loc, Msg, Args) ->
    halt(2).

-spec name_error(ast:loc(), string()) -> no_return().
name_error(Loc, Msg) -> name_error(Loc, Msg, []).

-spec bug(string()) -> no_return().
bug(Msg) ->
    halt(2).

-spec bug(string(), any()) -> no_return().
bug(Msg, Args) ->
    halt(2).

-spec uncovered_case(file:filename(), t:lineno(), any()) -> no_return().
uncovered_case(File, Line, X) ->
    halt(5).

-spec ty_error(ast:loc(), string(), any()) -> no_return().
ty_error(Loc, Msg, Args) ->
    halt(1).

-spec ty_error(ast:loc(), string()) -> no_return().
ty_error(Loc, Msg) -> ty_error(Loc, Msg, []).

-spec not_implemented(string()) -> no_return().
not_implemented(_Msg) -> halt(5).
