-module(subst).

-compile({no_auto_import,[apply/2]}).

-export_type([
    t/0
]).

-export([
    apply/2,
    domain/1,
    from_list/1
]).

-type t() :: #{ ast:ty_varname() => ast:ty() }.

-spec domain(t()) -> [ast:ty_varname()].
domain(S) -> maps:keys(S).

-spec apply(t(), ast:ty()) -> ast:ty().
apply(S, T) ->
    case T of
        {singleton, _} -> T;
        {binary, _, _} -> T;
        {empty_list} -> T;
        {list, U} -> {list, apply(S, U)};
        {nonempty_list, U} -> {nonempty_list, apply(S, U)};
        {improper_list, U, V} -> {improper_list, apply(S, U), apply(S, V)};
        {nonempty_improper_list, U, V} -> {nonempty_improper_list, apply(S, U), apply(S, V)};
        {fun_simple} -> T;
        {fun_any_arg, U} -> {fun_any_arg, apply(S, U)};
        {fun_full, Args, U} -> {fun_full, apply_list(S, Args), apply(S, U)};
        {range, _, _} -> T;
        {map_any} -> T;
        {map, Assocs} ->
            {map, lists:map(fun({Kind, U, V}) -> {Kind, apply(S, U), apply(S, V)} end, Assocs)};
        {predef, _} -> T;
        {predef_alias, _} -> T;
        {record, Name, Fields} ->
            {record, Name,
             lists:map(fun({FieldName, U}) -> {FieldName, apply(S, U)} end, Fields)};
        {named, Loc, Name, Args} ->
            {named, Loc, Name, apply_list(S, Args)};
        {tuple_any} -> T;
        {tuple, Args} -> {tuple, apply_list(S, Args)};
        {var, Alpha} ->
            case maps:find(Alpha, S) of
                error -> {var, Alpha};
                {ok, U} -> U
            end;
        {union, Args} -> {union, apply_list(S, Args)};
        {intersection, Args} -> {intersection, apply_list(S, Args)};
        {negation, U} -> {negation, apply(S, U)}
    end.

-spec apply_list(t(), [ast:ty()]) -> [ast:ty()].
apply_list(S, L) -> lists:map(fun(T) -> apply(S, T) end, L).

-spec from_list([{ast:ty_varname(), ast:ty()}]) -> t().
from_list(L) -> maps:from_list(L).
