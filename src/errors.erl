-module(errors).

-export([
    unsupported/3, unsupported/2,
    name_error/3, name_error/2,
    uncovered_case/3, bug/2, bug/1,
    ty_error/2, ty_error/3, ty_error/1, not_implemented/1, parse_error/1
]).

-spec generic_error(atom(), string()) -> no_return().
generic_error(Kind, Msg) -> throw({ety, Kind, Msg}).

-spec generic_error(atom(), ast:loc(), string(), string(), any()) -> no_return().
generic_error(Kind, Loc, Prefix, Msg, Args) ->
    generic_error(Kind,
                  utils:sformat("~s: ~s: ~s",
                                ast:format_loc(Loc), Prefix, utils:sformat(Msg, Args))).

-spec unsupported(ast:loc(), string(), any()) -> no_return().
unsupported(_Loc, _Msg, _Args) ->
  halt(5).

-spec unsupported(ast:loc(), string()) -> no_return().
unsupported(Loc, Msg) -> unsupported(Loc, Msg, []).

-spec name_error(ast:loc(), string(), any()) -> no_return().
name_error(Loc, Msg, Args) ->
  % names not supported yet
  halt(5).

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
    generic_error(ty_error, Loc, "Type error", Msg, Args).

-spec ty_error(ast:loc(), string()) -> no_return().
ty_error(Loc, Msg) -> ty_error(Loc, Msg, []).

-spec ty_error(string()) -> no_return().
ty_error(Msg) -> generic_error(ty_error, Msg).

-spec not_implemented(string()) -> no_return().
not_implemented(Msg) -> 
  halt(5).

-spec parse_error(string()) -> no_return().
parse_error(Msg) -> generic_error(parse_error, Msg).
