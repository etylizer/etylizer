
-module(ty_tuples).
-define(F(Z), fun() -> Z end).

-export([any/0, empty/0, var/1]).
-export([intersect/2, negate/1]).
-export([is_empty_corec/2, normalize_corec/3]).
-export([raw_transform/2, transform/2, substitute/3, all_variables/2, has_ref/2]).

empty() ->
  {dnf_var_ty_tuple:empty(), #{}}.

any() ->
  {dnf_var_ty_tuple:any(), #{}}.

var(Var) ->
  {dnf_var_ty_tuple:var(Var), #{}}.

normalize_corec({Default, AllTuples}, Fixed, M) ->
  Others = ?F(
    maps:fold(fun(Size, V, Acc) ->
      constraint_set:meet(
        ?F(Acc),
        ?F(dnf_var_ty_tuple:normalize_corec(Size, V, Fixed, M))
      )
              end, [[]], AllTuples)
  ),

  DF = ?F(dnf_var_ty_tuple:normalize_corec({default, maps:keys(AllTuples)}, Default, Fixed, M)),

  constraint_set:meet(
    DF,
    Others
  ).

is_empty_corec({Default, AllTuples}, M) ->
  dnf_var_ty_tuple:is_empty_corec(Default, M)
    andalso
  maps:fold(fun(_Size, V, Acc) -> Acc andalso dnf_var_ty_tuple:is_empty_corec(V, M) end, true, AllTuples).

negate({DT, T}) ->
  { dnf_var_ty_tuple:negate(DT), maps:map(fun(_K,V) -> dnf_var_ty_tuple:negate(V) end, T) }.


intersect({DefaultT1, T1}, {DefaultT2, T2}) ->
  % get all keys
  AllKeys = maps:keys(T1) ++ maps:keys(T2),
  IntersectKey = fun(Key) ->
    dnf_var_ty_tuple:intersect(
      maps:get(Key, T1, DefaultT1),
      maps:get(Key, T2, DefaultT2)
    )
                 end,
  {dnf_var_ty_tuple:intersect(DefaultT1, DefaultT2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.

raw_transform({DefaultT, T}, Ops = #{negate := Negate, union := Union, intersect := Intersect, any_tuple_i := AnyTupleI}) ->
  X1 = dnf_var_ty_tuple:raw_transform(DefaultT, Ops),
  Xs = lists:map(fun({Size, Tuple}) -> 
    case dnf_var_ty_tuple:raw_transform(Tuple, Ops) of
      {predef, any} -> AnyTupleI(Size);
      X -> X
    end
  end, maps:to_list(T)),

  Union([Intersect([X1, Negate(Union(Xs))]), Union(Xs)]).

transform({DefaultT, T}, Ops = #{any_tuple_i := AnyTupleI, any_tuple := Tuples, negate := Negate, union := Union, intersect := Intersect}) ->
  X1 = dnf_var_ty_tuple:transform(DefaultT, Ops),
  Xs = lists:map(fun({Size, Tup}) ->
    % if a tuple is semantically equivalent to empty, return empty instead of the empty tuple
    case dnf_var_ty_tuple:is_empty_corec(Tup, #{}) of
      true -> dnf_var_ty_tuple:transform(dnf_var_ty_tuple:empty(), Ops);
      _ -> 
        case dnf_var_ty_tuple:transform(Tup, Ops) of
          {predef, any} -> AnyTupleI(Size);
          X -> X
        end
    end
                 end, maps:to_list(T)),
  Sizes = maps:keys(T),

  DefaultTuplesWithoutExplicitTuples = Intersect([X1, Tuples(), Negate(Union([AnyTupleI(I) || I <- Sizes]))]),
  Union([DefaultTuplesWithoutExplicitTuples, Union(Xs)]).

substitute({DefaultTuple, AllTuples}, SubstituteMap, Memo) ->
  % substitute default tuple, get a new default tuple
%%  NewDefaultTuple = dnf_var_ty_tuple:csubstitute( fun(Ty) -> pi({tuple, default}, Ty) end, {tuple, default}, DefaultTuple, SubstituteMap, Memo),
  NewDefaultTuple = dnf_var_ty_tuple:substitute(DefaultTuple, SubstituteMap, Memo, fun(Ty) -> ty_rec:pi({tuple, default}, Ty) end),

  % the default tuple can be substituted to contain other explicit tuple lengths
  % example: {alpha, 0} with alpha := {1,1} ==> {0, 2 -> {1,1}}
  % projecting just the default tuple value 0 loses information
  % we need to get these explicit tuple lengths out of the substituted default tuple:
  % get all lengths after substitution,
  % and substitute the default tuple for each length,
  % filtering with the appropriate length projection function
  AllVars = dnf_var_ty_tuple:all_variables(DefaultTuple),
  % note: OtherTupleKeys not be included in the AllTuples keys, they are known
  % TODO erlang 26 map comprehensions
  Keys = maps:fold(fun(K,V,AccIn) -> case lists:member(K, AllVars) of true -> ty_rec:tuple_keys(V) -- maps:keys(AllTuples) ++ AccIn; _ -> AccIn end end, [], SubstituteMap),
  % Keys = [(tuple_keys(V) -- maps:keys(AllTuples)) || K := V <- SubstituteMap, lists:member(K, AllVars)],
  OtherTupleKeys = lists:usort(lists:flatten(Keys)),
  NewDefaultOtherTuples = maps:from_list([{Length, dnf_var_ty_tuple:substitute(DefaultTuple, SubstituteMap, Memo, fun(Ty) -> ty_rec:pi({tuple, Length}, Ty) end)} || Length <- OtherTupleKeys]),

  % all explicit keys are now all defined tuples and all newly explicit tuples after default substitution
  AllKeys = maps:keys(AllTuples) ++ maps:keys(NewDefaultOtherTuples),

  % {alpha, 0 => alpha} with alpha := {1} ==> {0, 1 => {1}}
  % for explicit tuples, collect all other lengths into a new map, yielding a list of maps
  % merge (union) these maps into NewOtherTuples
  NewOtherTuples = maps:from_list(lists:map(fun(Key) ->
    {Key, case maps:is_key(Key, AllTuples) of
            true ->
            dnf_var_ty_tuple:substitute(maps:get(Key, AllTuples), SubstituteMap, Memo, fun(Ty) -> ty_rec:pi({tuple, Key}, Ty) end);
            _ -> maps:get(Key, NewDefaultOtherTuples, NewDefaultTuple)
          end}
                                            end, AllKeys)),

  {NewDefaultTuple, NewOtherTuples}.

all_variables({Default, Others}, M) when is_map(Others) ->
  lists:usort(lists:flatten(
    dnf_var_ty_tuple:all_variables(Default, M) ++
    lists:map(fun({_K,V}) -> dnf_var_ty_tuple:all_variables(V, M) end, maps:to_list(Others))
  ));
all_variables(Ty, M) -> dnf_var_ty_tuple:all_variables(Ty, M).

has_ref({Default, AllTuple}, TyRef) ->
  false = dnf_var_ty_tuple:has_ref(Default, TyRef), % should never happen
  maps:fold(fun(_K,T, All) -> All orelse dnf_var_ty_tuple:has_ref(T, TyRef) end, false, AllTuple).