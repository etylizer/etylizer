-module(ty_map).

compare(A, B) -> ty_tuple:compare(A, B).
equal(P1, P2) -> ty_tuple:equal(P1, P2).
map(TupPart, FunPart) -> ty_tuple:tuple([TupPart, FunPart]).
%empty(Size) -> ty_tuple:empty(Size).
%any(Size) -> ty_tuple:any(Size).
%components(T) -> ty_tuple:components(T).
%pi(I, T) -> ty_tuple:pi(I, T).
%big_intersect(X) -> ty_tuple:big_intersect(X).

unparse({ty_tuple, 2, [TupPart, FunPart]}, ST0) ->
  % MandatoryAndOptional = ast_lib:erlang_ty_to_ast(Tup),
  % this is a bit messy
  % the map representation depends on a synactical representation of tuples and functions
  % but unparsing returns a semantical unparsed representation with simplifications
  {MandatoryAndOptional, ST1} = ty_node:unparse(TupPart, ST0),
  % Mandatory = ast_lib:erlang_ty_to_ast(Funs),
  {Mandatory, ST2} = ty_node:unparse(FunPart, ST1),
  {{map, split_into_associations(Mandatory, MandatoryAndOptional)}, ST2}.

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
            io:format(user,"~nGot:~p~n", [Got]),
            errors:bug("Internal map representation error")
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
    errors:bug("Illegal internal map representation").
