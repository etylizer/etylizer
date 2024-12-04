-module(tyutils).

-export([
    free_in_ty/1,
    %free_in_ty_scheme/1,
    %free_in_poly_env/1,
    free_in_subty_constrs/1
]).

-spec free_in_ty(ast:ty()) -> sets:set(ast:ty_varname()).
free_in_ty(T) ->
    L = utils:everything(fun (U) ->
                                 case U of
                                     {var, X} -> {ok, X};
                                     _ -> error
                                 end
                         end, T),
    sets:from_list(L).

-spec free_in_subty_constr(constr:simp_constr()) -> sets:set(ast:ty_varname()).
free_in_subty_constr(C) ->
    case C of
        {scsubty, _Locs, T1, T2} -> sets:union(free_in_ty(T1), free_in_ty(T2))
    end.

-spec free_in_subty_constrs(constr:simp_constrs()) -> sets:set(ast:ty_varname()).
free_in_subty_constrs(Cs) ->
    sets:fold(
        fun (C, Acc) -> sets:union(Acc, free_in_subty_constr(C)) end,
        sets:new(),
        Cs).
