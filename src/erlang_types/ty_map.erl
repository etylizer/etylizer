-module(ty_map).

-export([
  equal/2,
  compare/2,
  map/2,
  unparse/2
]).

-export_type([type/0]).

-type type() :: ty_tuple:type().
-type ast_ty() :: ast:ty().

-spec compare(type(), type()) -> lt | gt | eq.
compare(A, B) -> ty_tuple:compare(A, B).

-spec equal(type(), type()) -> boolean().
equal(A, B) -> compare(A, B) == eq.

-spec map(N, N) -> type() when N :: ty_node:type().
map(TupPart, FunPart) -> ty_tuple:tuple([TupPart, FunPart]).

-dialyzer(no_opaque).
-spec unparse(type(), T) -> {ast_ty(), T}.
unparse({ty_tuple, 2, [TupPart, FunPart]}, ST0) ->
  % FIXME this is messy and hacky
  % the map representation depends on a synactical representation of tuples and functions
  % but unparsing returns a semantical unparsed representation with simplifications
  % manually unfold the type and hope for the best
  {leaf, TyTupPart0} = ty_node:load(TupPart),
  % remove the part that makes the tuple part always non-empty
  TyTupPart = ty_rec:difference(TyTupPart0, ty_rec:atom(dnf_ty_atom:finite(['empty_map']))),
  {MandatoryAndOptional, ST1} = case TyTupPart of
    empty -> {{predef, none}, ST0};
    _ -> 
      {_, #{2 := TuplesDnf}} = ty_rec:pi(TyTupPart, ty_tuples),
      TDnf = dnf_ty_tuple:minimize_dnf(dnf_ty_tuple:dnf(TuplesDnf)),

      % negative part should be empty always, and only a single positive tuple remaining
      ToUnparse = [PosTup || {[PosTup], [], 1} <- TDnf], 
      {Z, ZZ} = lists:foldl(fun(T, {Tuples, ST00}) -> {Tp, ST01} = ty_tuple:unparse(T, ST00), {Tuples ++ [Tp], ST01} end, {[], ST0}, ToUnparse),
      {{union, Z}, ZZ}
  end,

  {leaf, TyFunPart} = ty_node:load(FunPart),
  TyFuns = ty_rec:pi(TyFunPart, ty_functions),
  {Mandatory, ST2} = case TyFuns of
    {{leaf, 1}, #{}} -> {{fun_simple}, ST1};
    {_, #{1 := FunsDnf}} -> 
      [{AllFuns, [], 1}] = dnf_ty_function:minimize_dnf(dnf_ty_function:dnf(FunsDnf)),
      {Conv, ST3} = lists:foldl(fun(F, {Funs, ST00}) -> {Fp, ST01} = ty_function:unparse(F, ST00), {Funs ++ [Fp], ST01} end, {[], ST1}, AllFuns),
      {{intersection, Conv}, ST3}
  end,
  {{map, split_into_associations(Mandatory, MandatoryAndOptional)}, ST2}.

% depends on ast:ty() internals
-spec split_into_associations(ast_ty(), ast_ty()) -> [ast:ty_map_assoc()].
split_into_associations({fun_simple}, OnlyOptional) ->
    % only optional associations
    case OnlyOptional of
        {predef, none} ->
            [];
        % {tuple, [X, Y]} -> 
        %     [{map_field_opt, X, Y}];
        {union, Tuples} -> 
            [{map_field_opt, X, Y} || {tuple, [X, Y]} <- Tuples]
        % Got -> 
        %     io:format(user,"~nGot:~p~n", [Got]),
        %     errors:bug("Internal map representation error")
    end;
split_into_associations({intersection, Funs}, {union, Tups}) ->
    RawFun = [{A, B} || {fun_full, [A], B} <- Funs],
    RawTuple = [{A, B} || {tuple, [A, B]} <- Tups, not lists:member({A, B}, RawFun)],
    true = (length(Tups) - length(Funs) =:= length(RawTuple)),
    [{map_field_req, A, B} || {A, B} <- RawFun] 
        ++ 
    [{map_field_opt, A, B} || {A, B} <- RawTuple];
% split_into_associations(F = {fun_full, [_], _}, T = {tuple, [_, _]}) ->
%     split_into_associations({intersection, [F]}, {union, [T]});
split_into_associations(Mandatory, MandatoryAndOptional) ->
    io:format(user,"Mandatory: ~p~n", [Mandatory]),
    io:format(user,"Mandatory and opt: ~p~n", [MandatoryAndOptional]),
    errors:bug("Illegal internal map representation").
