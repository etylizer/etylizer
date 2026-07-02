-module(subst).

-compile({no_auto_import,[apply/3]}).

-include("log.hrl").

-export_type([
    t/0,
    base_subst/0,
    tally_subst/0
]).

-export([
    apply/3,
    apply_base/2,
    from_list/1,
    empty/0,
    extend/3,
    mk_tally_subst/2,
    base_subst/1,
    collect_vars/4,
    clean_cons/3
]).

-ifdef(TEST).
-export([
    clean/3
]).
-endif.


-type base_subst() :: #{ ast:ty_varname() => ast:ty() }.

-type tally_subst() :: {tally_subst, base_subst(), sets:set(ast:ty_varname())}.

-type t() :: base_subst() | tally_subst().

-include("etylizer.hrl").

-spec base_subst(t()) -> base_subst().
base_subst({tally_subst, S, _}) -> S;
base_subst(S) -> S.

-spec clean(ast:ty(), sets:set(ast:ty_varname()), symtab:t()) -> ast:ty().
clean(T, Fixed, SymTab) ->
    % clean
    Cleaned = clean_type(T, Fixed, SymTab),
    % simplify by converting into internal type and back (processes any() and none() replacements)
    X = ty_parser:parse(Cleaned),
    Res = ty_parser:unparse(X),
    % FIXME remove sanity at some point
    ?assert_pattern(true, ty_node:leq(X, ty_parser:parse(T))),
    Res.

-spec clean_cons([{ast:ty(), ast:ty()}], sets:set(ast:ty_varname()), symtab:t()) -> [{ast:ty(), ast:ty()}].
clean_cons(CList, Fixed, SymTab) ->
    Unfold = fun(Ty) -> ast_utils:unfold_ty(SymTab, Ty) end,
    UnfoldedCList = [{Unfold(C1), Unfold(C2)} || {C1, C2} <- CList],
    VarPositions = collect_vars_clist(UnfoldedCList, 0, #{}, Fixed),

    Apply = fun(Ty) -> maps:fold(
        fun(VariableName, VariablePositions, Tyy) ->
            case lists:usort(VariablePositions) of
                [0] -> apply_base(#{VariableName => {predef, none}}, Tyy);
                [1] -> apply_base(#{VariableName => {predef, any}}, Tyy);
                _ -> Tyy
            end
        end, Ty, VarPositions)
            end,

    [{Apply(C1), Apply(C2)} || {C1, C2} <- CList].

-type clean_mode() :: {clean, symtab:t()} | no_clean.

-spec apply(t(), ast:ty(), clean_mode()) -> ast:ty().
apply(Subst = {tally_subst, BaseSubst, Fixed}, T, CleanMode) ->
    U = apply_base(BaseSubst, T),
    Res =
        case CleanMode of
            {clean, SymTab} -> clean(U, Fixed, SymTab);
            no_clean -> U
        end,
    ?LOG_TRACE("subst:apply, T=~s, Subst=~s, U=~s, Res=~s",
        pretty:render_ty(T),
        pretty:render_subst(Subst),
        pretty:render_ty(U),
        pretty:render_ty(Res)),
    Res;
apply(S, T, _) -> apply_base(S, T).

-spec apply_base(base_subst(), ast:ty()) -> ast:ty().
apply_base(S, T) ->
    case T of
        {singleton, _} -> T;
        {bitstring} -> T;
        {bitstring, _, _} -> T;
        {empty_list} -> T;
        {fun_simple} -> T;
        {range, _, _} -> T;
        {map_any} -> T;
        {predef, _} -> T;
        {predef_alias, _} -> T;
        {tuple_any} -> T;
        {mu_var, _} -> T;
        {var, Alpha} ->
            case maps:find(Alpha, S) of
                error -> {var, Alpha};
                {ok, U} -> U
            end;
        _ -> apply_base_rec(S, T)
    end.

-spec apply_base_rec(base_subst(), ast:ty()) -> ast:ty().
apply_base_rec(S, T) ->
    case T of
        {cons, A, B} -> {cons, apply_base(S, A), apply_base(S, B)};
        {list, U} -> {list, apply_base(S, U)};
        {mu, V, U} -> {mu, V, apply_base(S, U)};
        {nonempty_list, U} -> {nonempty_list, apply_base(S, U)};
        {improper_list, U, V} -> {improper_list, apply_base(S, U), apply_base(S, V)};
        {nonempty_improper_list, U, V} -> {nonempty_improper_list, apply_base(S, U), apply_base(S, V)};
        {fun_any_arg, U} -> {fun_any_arg, apply_base(S, U)};
        {fun_full, Args, U} -> {fun_full, apply_list(S, Args), apply_base(S, U)};
        _ -> apply_base_rec2(S, T)
    end.

-spec apply_base_rec2(base_subst(), ast:ty()) -> ast:ty().
apply_base_rec2(S, T) ->
    case T of
        {named, Loc, Ref, Args} ->
            {named, Loc, Ref, apply_list(S, Args)};
        {map, Assocs} ->
            {map, lists:map(fun({Kind, U, V}) -> {Kind, apply_base(S, U), apply_base(S, V)} end, Assocs)};
        {tuple, Args} -> {tuple, apply_list(S, Args)};
        {union, Args} -> {union, apply_list(S, Args)};
        {intersection, Args} -> {intersection, apply_list(S, Args)};
        {negation, U} -> {negation, apply_base(S, U)};
        _ -> T
    end.

-spec apply_list(base_subst(), [ast:ty()]) -> [ast:ty()].
apply_list(S, L) -> lists:map(fun(T) -> apply_base(S, T) end, L).

-spec extend(t(), ast:ty_varname(), ast:ty()) -> t().
extend({tally_subst, BaseSubst, Fixed}, Alpha, T) ->
    {tally_subst, maps:put(Alpha, T, BaseSubst), Fixed};
extend(BaseSubst, Alpha, T) ->
    maps:put(Alpha, T, BaseSubst).

-spec from_list([{ast:ty_varname(), ast:ty()}]) -> t().
from_list(L) -> maps:from_list(L).

-spec empty() -> t().
empty() -> #{}.

-spec mk_tally_subst(sets:set(ast:ty_varname()), base_subst()) -> tally_subst().
mk_tally_subst(Fixed, Base) -> {tally_subst, Base, Fixed}.

-spec clean_type(ast:ty(), sets:set(ast:ty_varname()), symtab:t()) -> ast:ty().
clean_type(Ty, Fix, SymTab) ->
    %% collect ALL vars in all positions
    %% if a var is only in co variant position, replace with 0
    %% if a var is only in contra variant position, replace with 1
    UnfoldedTy = ast_utils:unfold_ty(SymTab, Ty),
    VarPositions = collect_vars(UnfoldedTy, 0, #{}, Fix),

    NoVarsDnf = maps:fold(
        fun(VariableName, VariablePositions, Tyy) ->
            case lists:usort(VariablePositions) of
                [0] ->
                    % !a => none
                    %  a => none
                    % FIXME (SW, 2023-12-08): this has bad performance. Better build one substitution
                    % and apply it once.
                    R = apply_base(#{VariableName => {predef, none}}, Tyy),
                    R;
                [1] ->
                    apply_base(#{VariableName => {predef, any}}, Tyy);
                _ -> Tyy
            end
        end, Ty, VarPositions),

    Cleaned = NoVarsDnf,
    Cleaned.


-spec flip_pos(0 | 1) -> 0 | 1.
flip_pos(0) -> 1;
flip_pos(1) -> 0.


% Operates on unfolded types (named types already resolved, recursive refs are {ty_hole}).
% Callers must unfold via ast_utils:unfold_ty/2 before calling.
-spec collect_vars_clist([{ast:ty() | {ty_hole}, ast:ty() | {ty_hole}}], 0 | 1, #{ast:ty_varname() => [0 | 1]}, sets:set(ast:ty_varname())) ->
    #{ast:ty_varname() => [0 | 1]}.
collect_vars_clist(L, CPos, Pos, Fix) when is_list(L) ->
    lists:foldl(fun({C1, C2}, Acc) ->
        Acc1 = collect_vars(C1, CPos, Acc, Fix),
        collect_vars(C2, flip_pos(CPos), Acc1, Fix)
                end, Pos, L).

-spec collect_vars(ast:ty() | {ty_hole}, 0 | 1, #{ast:ty_varname() => [0 | 1]}, sets:set(ast:ty_varname())) ->
    #{ast:ty_varname() => [0 | 1]}.
collect_vars(Ty, CPos, Pos, Fix) ->
    case Ty of
        {map, _} ->
            collect_vars(ty_parser:rewrite_map_to_representation(Ty), CPos, Pos, Fix);
        {predef, _} -> Pos;
        {predef_alias, _} -> Pos;
        {singleton, _} -> Pos;
        {range, _, _} -> Pos;
        {_, any} -> Pos;
        {empty_list} -> Pos;
        {bitstring} -> Pos;
        {bitstring, _, _} -> Pos;
        {map_any} -> Pos;
        {tuple_any} -> Pos;
        {fun_simple} -> Pos;
        {mu_var, _} -> Pos;
        {ty_hole} -> Pos;
        {var, Name} ->
            case sets:is_element(Name, Fix) of
                true -> Pos;
                _ ->
                    AllPositions = maps:get(Name, Pos, []),
                    Pos#{Name => lists:uniq(AllPositions ++ [CPos])}
            end;
        _ -> collect_vars_rec(Ty, CPos, Pos, Fix)
    end.

-spec collect_vars_rec(ast:ty() | {ty_hole}, 0 | 1, #{ast:ty_varname() => [0 | 1]}, sets:set(ast:ty_varname())) ->
    #{ast:ty_varname() => [0 | 1]}.
collect_vars_rec(Ty, CPos, Pos, Fix) ->
    case Ty of
        {K, Components} when K == union; K == intersection; K == tuple ->
            lists:foldl(fun(T, Acc) -> collect_vars(T, CPos, Acc, Fix) end, Pos, Components);
        {fun_full, Components, Target} ->
            Acc1 = lists:foldl(fun(T, Acc) -> collect_vars(T, flip_pos(CPos), Acc, Fix) end, Pos, Components),
            collect_vars(Target, CPos, Acc1, Fix);
        {negation, A} -> collect_vars(A, flip_pos(CPos), Pos, Fix);
        {nonempty_improper_list, A, B} ->
            Acc1 = collect_vars(A, CPos, Pos, Fix),
            collect_vars(B, CPos, Acc1, Fix);
        {nonempty_list, A} -> collect_vars(A, CPos, Pos, Fix);
        {list, A} -> collect_vars(A, CPos, Pos, Fix);
        {mu, _MuVar, A} -> collect_vars(A, CPos, Pos, Fix);
        {cons, A, B} ->
            Acc1 = collect_vars(A, CPos, Pos, Fix),
            collect_vars(B, CPos, Acc1, Fix);
        {improper_list, A, B} ->
            Acc1 = collect_vars(A, CPos, Pos, Fix),
            collect_vars(B, CPos, Acc1, Fix);
        _ ->
            logger:error("Unhandled collect vars branch: ~p", [Ty]),
            errors:bug("Unhandled collect vars branch: ~p", [Ty])
    end.

