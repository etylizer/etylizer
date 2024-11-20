-module(typing_common).

-export([
    mono_ty/2,
    mono_ty/3,
    mono_ty/4,
    format_src_loc/1
]).

-export_type([ctx/0]).

-include("log.hrl").
-include("typing.hrl").

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
-spec mono_ty(ast:loc(), ast:ty_scheme()) -> {ast:ty(), sets:set(ast:ty_varname()), integer() | no_fresh}.
mono_ty(L, TyScm) -> mono_ty(L, TyScm, no_fresh).

-spec fresh_tyvar(ast:ty_varname(), integer() | no_fresh) ->
          {ast:ty_varname(), integer() | no_fresh}.
fresh_tyvar(Alpha, no_fresh) -> {Alpha, no_fresh};
fresh_tyvar(Alpha, I) ->
    AlphaFresh = list_to_atom(utils:sformat("~w#~w", Alpha, I)),
    {AlphaFresh, I + 1}.

% Creates the monomorphic version of the given type scheme.
%
% We first replace each type variable with its bound, see EEP-71
% (https://www.erlang.org/eeps/eep-0071)). As a heuristic, we do not replace a variable
% if the bound is term() or any(). Reason: many type spec in OTP add the bound term() without
% the intention of treating the type variable as an alias for term(), see
% https://github.com/erlang/otp/pull/8736
% In order to perform the replacement, we require the dependencies between type variables and
% their bounds to be acyclic. For example, the following is not allowed:
% 'when A :: [B], B :: [A]'
%
% The next steps then replaces each type variable that is still present with a fresh
% type variable.
-spec mono_ty(ast:loc(), ast:ty_scheme(), integer() | no_fresh) ->
    {ast:ty(), sets:set(ast:ty_varname()), integer() | no_fresh}.
mono_ty(L, TyScm, FreshStart) ->
    mono_ty(L, TyScm, FreshStart, fun fresh_tyvar/2).

-type fresh_fun(State) :: fun((ast:ty_varname(), State) -> {ast:ty_varname(), State}).

-spec order_bounds([ast:bound_tyvar()]) -> [ast:bounded_tyvar()] | cyclic.
order_bounds(BoundedTyvars) ->
    VarOrder =
        graph:with_graph(
            fun(G) ->
                % add all type variables as vertices
                lists:foreach(
                    fun({Alpha, _Bound}) ->
                        graph:add_vertex(G, Alpha)
                    end,
                    BoundedTyvars),
                % add an edge Beta -> Alpha if Beta is free in Alpha's bound
                lists:foreach(
                    fun({Alpha, Bound}) ->
                        Free = sets:to_list(tyutils:free_in_ty(Bound)),
                        lists:map( fun(Beta) -> graph:add_edge(G, Beta, Alpha) end, Free)
                    end,
                    BoundedTyvars),
                L = graph:topsort(G),
                ?LOG_TRACE("Graph: ~200p, L: ~200p", graph:to_list(G, fun atom_to_list/1), L),
                L
            end),
    case VarOrder of
        cyclic -> cyclic;
        L ->
            lists:map(
                fun(Alpha) ->
                    case lists:keyfind(Alpha, 1, BoundedTyvars) of
                        false -> errors:bug("variable not found");
                        {_, Bound} -> {Alpha, Bound}
                    end
                end,
                L)
    end.

-spec is_any_bound(ast:ty()) -> boolean().
is_any_bound({predef, any}) -> true;
is_any_bound({predef_alias, term}) -> true;
is_any_bound(_) -> false.

% assumes that the bounds are already ordered so that if {Beta, Bound} is in the list of
% bounds and Alpha is free in Bound, the Alpha appears in the list of bounds before Beta,
-spec replace_bounds([ast:bound_tyvar()], [ast:ty_varname()], subst:t(), fresh_fun(State), State) ->
    {[ast:ty_varname()], subst:t(), State}.
replace_bounds([], Polys, Subst, State, _FreshFun) ->
    {lists:reverse(Polys), Subst, State};
replace_bounds([{Alpha, Bound} | Rest], Polys, Subst, State, FreshFun) ->
    case is_any_bound(Bound) of
        true  ->
            {Fresh, NewState} = FreshFun(Alpha, State),
            NewSubst = subst:extend(Subst, Alpha, {var, Fresh}),
            replace_bounds(Rest, [Fresh | Polys], NewSubst, NewState, FreshFun);
        false ->
            NewSubst = subst:extend(Subst, Alpha, subst:apply(Subst, Bound)),
            replace_bounds(Rest, Polys, NewSubst, State, FreshFun)
    end.

-spec mono_ty(ast:loc(), ast:ty_scheme(), State, fresh_fun(State)) ->
    {ast:ty(), sets:set(ast:ty_varname()), State}.
mono_ty(Loc, TyScm = {ty_scheme, Bounds, T}, FreshStart, FreshFun) ->
    ?LOG_TRACE("Monomorphizing type scheme ~s", pretty:render_tyscheme(TyScm)),
    case order_bounds(Bounds) of
        cyclic ->
            errors:ty_error(Loc,
                "Cyclic bounds in type spec: ~s", [pretty:render_tyscheme(TyScm)]);
        OrderedBounds ->
            ?LOG_TRACE("Ordered bounds: ~200p", OrderedBounds),
            {Fresh, Subst, NewState} =
                replace_bounds(OrderedBounds, [], subst:empty(), FreshStart, FreshFun),
            Res = subst:apply(Subst, T),
            ?LOG_TRACE("Result of monomorphizing type scheme ~s:~n~s~nRaw: ~w~nFresh: ~200p",
               pretty:render_tyscheme(TyScm), pretty:render_ty(Res), Res, Fresh),
            {Res, sets:from_list(Fresh), NewState}
    end.
