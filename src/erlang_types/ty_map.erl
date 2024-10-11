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


transform({ty_tuple, 2, [Tup, Funs]}, _O = #{to_tuple := _ToTuple}) ->
    Mandatory = ast_lib:erlang_ty_to_ast(Funs),
    MandatoryAndOptional = ast_lib:erlang_ty_to_ast(Tup),
    {map, split_into_associations(Mandatory, MandatoryAndOptional)}.
    %io:format(user,"~s~n", [ty_rec:print(Tup)]),
    %io:format(user,"~s~n", [ty_rec:print(Fus)]),
    %error(todo_map_transform).
     
% FIXME use O map converting functions
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
split_into_associations(_Mandatory, _MandatoryAndOptional) ->
    % mandatory are intersection of functions
    error(mandatory_not_implemented).

substitute({ty_tuple, Dim, Refs}, Map, Memo) ->
    {ty_tuple, Dim, [ ty_rec:substitute(B, Map, Memo) || B <- Refs ] }.

all_variables(T, M) -> ty_tuple:all_variables(T, M).