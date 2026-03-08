-module(ty_map).

-export([
  equal/2,
  compare/2,
  map/2,
  unparse/2
]).

% invariants
-etylizer({disable_exhaustiveness_toplevel, [unparse/2]}).

-include("erlang_types.hrl").

-export_type([type/0]).

-type type() :: ty_tuple:type().

-spec compare(type(), type()) -> lt | gt | eq.
compare(A, B) -> ty_tuple:compare(A, B).

-spec equal(type(), type()) -> boolean().
equal(A, B) -> compare(A, B) == eq.

-spec map(N, N) -> type() when N :: ty_node:type().
map(TupPart, FunPart) -> ty_tuple:tuple([TupPart, FunPart]).

-spec unparse(type(), T) -> {ast_ty(), T} when T :: unparse_cache().
unparse({ty_tuple, 2, [TupPart, FunPart]}, ST0) ->
  % FIXME this is messy and hacky
  % the map representation depends on a synactical representation of tuples and functions
  % but unparsing returns a semantical unparsed representation with simplifications
  % manually unfold the type and hope for the best
  
  {MandatoryAndOptional, ST1} = unparse_tuple_part(TupPart, ST0),
  {Mandatory, ST2} = unparse_fun_part(FunPart, ST1),

  {{map, split_into_associations(Mandatory, MandatoryAndOptional)}, ST2}.

-spec unparse_fun_part(ty_node:type(), S) -> {ast_ty(), S} when S :: unparse_cache().
unparse_fun_part(FunPart, ST) ->
    % a map should definitely not have any variables
    {leaf, TyFunPart} = case ty_node:load(FunPart) of 
                             {leaf, TyFunPart1} -> {leaf, TyFunPart1}; 
                             _ -> error(badarg) 
                         end, % non-exhaustive
    case TyFunPart of
        empty -> error(badarg);
        any -> error(badarg);
        TyFunRecord ->
            TyFuns = ty_rec:pi(TyFunRecord, ty_functions),
            case TyFuns of
              {{leaf, 1}, #{}} -> {{fun_simple}, ST};
              {_, #{1 := FunsDnf}} -> unparse_fun_part_dnf(FunsDnf, ST);
                _ -> error(badarg)
            end
    end.

-spec unparse_fun_part_dnf(dnf_ty_function:type(), S) -> {ast_ty(), S} when S :: unparse_cache().
unparse_fun_part_dnf(FunsDnf, ST) ->
    [{AllFuns, [], 1}] = 
    case dnf_ty_function:minimize_dnf(dnf_ty_function:dnf(FunsDnf)) of
        R = [{_, [], 1}] -> R;
        _ -> error(badarg)
    end,
    {Conv, ST3} = lists:foldl(fun(F, {Funs, ST00}) -> {Fp, ST01} = ty_function:unparse(F, ST00), {Funs ++ [Fp], ST01} end, {[], ST}, AllFuns),
    {{intersection, Conv}, ST3}.

-spec unparse_tuple_part(ty_node:type(), S) -> {{predef, none} | {union, [ast:ty_tuple()]}, S} when S :: unparse_cache().
unparse_tuple_part(TupPart, ST) ->
    % a map should definitely not have any variables
    {leaf, TyTupPart0} = case ty_node:load(TupPart) of 
                             {leaf, TyTupPart1} -> {leaf, TyTupPart1}; 
                             _ -> error(badarg) 
                         end, % non-exhaustive

    % remove the part that makes the tuple part always non-empty
    TyTupPart = ty_rec:difference(TyTupPart0, ty_rec:atom(dnf_ty_atom:finite(['empty_map']))),

    case TyTupPart of
      empty -> {{predef, none}, ST};
      any -> error(badarg);
      _ -> unparse_tuple_part_dnf(TyTupPart, ST)
    end.

-spec unparse_tuple_part_dnf(ty_rec:type_record(), S) -> {{union, [ast:ty_tuple()]}, S} when S :: unparse_cache().
unparse_tuple_part_dnf(TyTupPart, ST) ->
    {_, #{2 := TuplesDnf}} =  % TODO mark as non-exhaustive
    case ty_rec:pi(TyTupPart, ty_tuples) of
        M = {_, #{2 := _}} -> M;
        _ -> error(badarg)
    end,

    TDnf = dnf_ty_tuple:minimize_dnf(dnf_ty_tuple:dnf(TuplesDnf)),

    % negative part should be empty always, and only a single positive tuple remaining
    ToUnparse = lists:map(fun({[PosTup], [], 1}) -> PosTup;(_) -> error(badarg) end, TDnf), %[PosTup || {[PosTup], [], 1} <- TDnf], 
    unparse_tuple_part_dnf_unparse(ToUnparse, ST).

-spec unparse_tuple_part_dnf_unparse([ty_tuple:type()], S) -> {{union, [ast:ty_tuple()]}, S} when S :: unparse_cache().
unparse_tuple_part_dnf_unparse(ToUnparse, ST) ->
    {Z, ZZ} = lists:foldl(fun(T, {Tuples, ST00}) -> {Tp, ST01} = ty_tuple:unparse(T, ST00), {Tuples ++ [Tp], ST01} end, {[], ST}, ToUnparse),
    {{union, Z}, ZZ}.

% depends on ast:ty() internals
-spec split_into_associations(ast_ty(), {predef, none} | {union, [ast:ty_tuple()]}) -> [ast:ty_map_assoc()].
split_into_associations({fun_simple}, OnlyOptional) ->
    split_into_associations_only_optional(OnlyOptional);
split_into_associations({intersection, Funs}, {union, Tups}) ->
    split_into_associations_both(Funs, Tups);
% split_into_associations(F = {fun_full, [_], _}, T = {tuple, [_, _]}) ->
%     split_into_associations({intersection, [F]}, {union, [T]});
split_into_associations(Mandatory, MandatoryAndOptional) ->
    io:format(user,"Mandatory: ~p~n", [Mandatory]),
    io:format(user,"Mandatory and opt: ~p~n", [MandatoryAndOptional]),
    errors:bug("Illegal internal map representation").

-spec split_into_associations_both([ast_ty()], [ast_ty()]) -> [ast:ty_map_assoc()].
split_into_associations_both(Funs, Tups) ->
    RawFun = [{A, B} || {fun_full, [A], B} <- Funs],
    RawTuple = [{A, B} || {tuple, [A, B]} <- Tups, not lists:member({A, B}, RawFun)],
    % true = (length(Tups) - length(Funs) =:= length(RawTuple)),
    [{map_field_req, A, B} || {A, B} <- RawFun]
        ++ 
    [{map_field_opt, A, B} || {A, B} <- RawTuple].

-spec split_into_associations_only_optional({predef, none} | {union, [ast:ty_tuple()]}) -> [ast:ty_map_assoc()].
split_into_associations_only_optional(OnlyOptional) ->
    case OnlyOptional of
        {predef, none} ->
            [];
        {union, Tuples} ->
            [{map_field_opt, X, Y} || {tuple, [X, Y]} <- Tuples]
        % Got -> 
        %     io:format(user,"~nGot:~p~n", [Got]),
        %     errors:bug("Internal map representation error")
    end.
