-module(typing_common).

-export([
    mono_ty/1,
    mono_ty/2,
    format_src_loc/1
]).

-export_type([ctx/0]).

-include_lib("log.hrl").
-include_lib("typing.hrl").

-spec format_src_loc(ast:loc()) -> string().
format_src_loc({loc, File, LineNo, ColumnNo}) ->
    ErrMsg = "",
    case utils:file_get_lines(File) of
        {error, _} -> ErrMsg;
        {ok, Lines} ->
            N = length(Lines),
            if
                LineNo >= 1 andalso LineNo =< N ->
                    Line = string:trim(lists:nth(LineNo, Lines), trailing),
                    ColumnSpace = lists:duplicate(ColumnNo - 1, $\s),
                    utils:sformat("%~5.B| ~s~n%     | ~s^", LineNo, Line, ColumnSpace);
                true ->
                    ErrMsg
            end
    end.

% Creates the monomorphic version of the given type scheme, does not
% replace the universally quantified type variables with fresh ones.
-spec mono_ty(ast:ty_scheme()) -> ast:ty().
mono_ty(TyScm) ->
    {U, _, _} = mono_ty(TyScm, no_fresh),
    U.

-spec fresh_tyvar(ast:ty_varname(), integer() | no_fresh) ->
          {ast:ty_varname(), integer() | no_fresh}.
fresh_tyvar(Alpha, no_fresh) -> {Alpha, no_fresh};
fresh_tyvar(Alpha, I) ->
    AlphaFresh = list_to_atom(utils:sformat("~w#~w", Alpha, I)),
    {AlphaFresh, I + 1}.

% Creates the monomorphic version of the given type scheme by replacing
% the universally quantified type variables with fresh type variables.
% The second parameter is the start number for the fresh type variable
% generator.
-spec mono_ty(ast:ty_scheme(), integer() | no_fresh) ->
          {ast:ty(), sets:set(ast:ty_varname()), integer() | no_fresh}.
mono_ty(TyScm = {ty_scheme, Tyvars, T}, FreshStart) ->
    ?LOG_DEBUG("Monomorphizing type scheme ~s", pretty:render_tyscheme(TyScm)),
    {Kvs, Freshs, I} =
        lists:foldl(
          fun({Alpha, Bound}, {Kvs, Freshs, I}) ->
                  {AlphaFresh, NextI} = fresh_tyvar(Alpha, I),
                  {[ {Alpha, ast_lib:mk_intersection([{var, AlphaFresh}, Bound])} | Kvs],
                   [ AlphaFresh | Freshs ],
                   NextI}
          end,
          {[], [], FreshStart},
          Tyvars
         ),
    Subst = subst:from_list(Kvs),
    Res = subst:apply(Subst, T),
    ?LOG_DEBUG("Result of monomorphizing type scheme ~s:~n~s~nFresh: ~200p",
               pretty:render_tyscheme(TyScm), pretty:render_ty(Res), Freshs),
    {Res, sets:from_list(Freshs), I}.


