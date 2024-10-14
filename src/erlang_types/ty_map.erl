-module(ty_map).

%% {ty, ty}
-export([compare/2, equal/2, substitute/3, all_variables/2]).

-export([map/2, has_ref/2, transform/2, any/0, empty/0]).

empty() -> {ty_tuple, 2, [ty_rec:empty(), ty_rec:empty()]}.
any() -> {ty_tuple, 2, [ty_rec:any(), ty_rec:any()]}.

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

map(TupPart,FunPart) -> {ty_tuple, 2, [TupPart, FunPart]}.

has_ref(Tup, Ref) -> ty_tuple:has_ref(Tup, Ref).


% FIXME #135
transform({ty_tuple, 2, [Tup, Funs]}, _O = #{to_map := ToMap}) ->
    Mandatory = ast_lib:erlang_ty_to_ast(Funs),
    MandatoryAndOptional = ast_lib:erlang_ty_to_ast(Tup),
    ToMap(split_into_associations(Mandatory, MandatoryAndOptional)).
     
split_into_associations({fun_simple}, OnlyOptional) ->
    % only optional associations
    case OnlyOptional of
        {predef, none} ->
            [];
        {tuple, [X, Y]} -> 
            [{map_field_opt, X, Y}];
        {union, Tuples} -> 
            [{map_field_opt, X, Y} || {tuple, [X, Y]} <- Tuples];
        Got -> 
            io:format(user,"Got:~p~n", [Got]),
            error(sanity_not_implemented)
    end;
split_into_associations({intersection, Funs}, {union, Tups}) ->
    RawFun = [{A, B} || {fun_full, [A], B} <- Funs],
    RawTuple = [{A, B} || {tuple, [A, B]} <- Tups, not lists:member({A, B}, RawFun)],
    true = (length(Tups) - length(Funs) =:= length(RawTuple)),
    [{map_field_req, A, B} || {A, B} <- RawFun] 
        ++ 
    [{map_field_opt, A, B} || {A, B} <- RawTuple];
split_into_associations(F = {fun_full, [_], _}, T = {tuple, [_, _]}) ->
    split_into_associations({intersection, [F]}, {union, [T]});
split_into_associations(Mandatory, MandatoryAndOptional) ->
    io:format(user,"Mandatory: ~p~n", [Mandatory]),
    io:format(user,"Mandatory and opt: ~p~n", [MandatoryAndOptional]),
    error(illegal_internal_map_representation).

substitute({ty_tuple, Dim, Refs}, Map, Memo) ->
    {ty_tuple, Dim, [ ty_rec:substitute(B, Map, Memo) || B <- Refs ] }.

all_variables(T, M) -> ty_tuple:all_variables(T, M).