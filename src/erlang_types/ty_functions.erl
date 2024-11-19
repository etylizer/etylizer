-module(ty_functions).
-define(F(Z), fun() -> Z end).

-export([any/0, empty/0, var/1]).
-export([intersect/2, negate/1]).
-export([is_empty_corec/2, normalize_corec/3]).
-export([transform/2, raw_transform/2, substitute/3, all_variables/2, has_ref/2]).

empty() ->
  {dnf_var_ty_function:empty(), #{}}.

any() ->
  {dnf_var_ty_function:any(), #{}}.

var(Var) ->
  {dnf_var_ty_function:var(Var), #{}}.

normalize_corec({Default, AllFunctions}, Fixed, M) ->
  Others = ?F(
    maps:fold(fun(Size, V, Acc) ->
      constraint_set:meet(
        ?F(Acc),
        ?F(dnf_var_ty_function:normalize_corec(Size, V, Fixed, M))
      )
              end, [[]], AllFunctions)
  ),

  DF = ?F(dnf_var_ty_function:normalize_corec({default, maps:keys(AllFunctions)}, Default, Fixed, M)),

  constraint_set:meet(
    DF,
    Others
  ).

is_empty_corec({Default, AllFunctions}, M) ->
  dnf_var_ty_function:is_empty_corec(Default, M)
    andalso
    maps:fold(fun(_Size, V, Acc) -> Acc andalso dnf_var_ty_function:is_empty_corec(V, M) end, true, AllFunctions).

negate({DF, F}) ->
  {dnf_var_ty_function:negate(DF), maps:map(fun(_K,V) -> dnf_var_ty_function:negate(V) end, F)}.
  
intersect({DefaultF1, F1}, {DefaultF2, F2}) ->
  % get all keys
  AllKeys = maps:keys(F1) ++ maps:keys(F2),
  IntersectKey = fun(Key) ->
    dnf_var_ty_function:intersect(
      maps:get(Key, F1, DefaultF1),
      maps:get(Key, F2, DefaultF2)
    )
                 end,
  {dnf_var_ty_function:intersect(DefaultF1, DefaultF2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.

raw_transform({DefaultF, F}, Ops = #{negate := Negate, union := Union, intersect := Intersect, any_function_i := AnyFunI}) ->
  X1 = dnf_var_ty_function:raw_transform(DefaultF, Ops),
  Xs = lists:map(fun({Size, Function}) -> 
    case dnf_var_ty_function:raw_transform(Function, Ops) of
      {predef, any} -> AnyFunI(Size);
      X -> X
    end
  end, maps:to_list(F)),

  Union([Intersect([X1, Negate(Union(Xs))]), Union(Xs)]).

transform({DefaultF, F}, Ops = #{any_function_i := AnyFunI, any_function := Functions, negate := Negate, union := Union, intersect := Intersect}) ->
  X1 = dnf_var_ty_function:transform(DefaultF, Ops),
  Xs = lists:map(fun({Size, Func}) -> 
    case dnf_var_ty_function:transform(Func, Ops) of
      {predef, any} -> AnyFunI(Size);
      X -> X
    end
  end, maps:to_list(F)),
  Sizes = maps:keys(F),

  DefaultFunctionsWithoutExplicitFunctions = Intersect([X1, Functions(), Negate(Union([AnyFunI(I) || I <- Sizes]))]),
  Union([DefaultFunctionsWithoutExplicitFunctions, Union(Xs)]).

substitute({DefaultFunction, AllFunctions}, SubstituteMap, Memo) ->
  % see multi_substitute for comments
  % TODO refactor abstract into one function for both tuples and funcions
  NewDefaultFunction = dnf_var_ty_function:substitute(DefaultFunction, SubstituteMap, Memo, fun(Ty) -> ty_rec:pi({function, default}, Ty) end),
  AllVars = dnf_var_ty_function:all_variables(DefaultFunction),
  % TODO erlang 26 map comprehensions
  Keys = maps:fold(fun(K,V,AccIn) -> case lists:member(K, AllVars) of true -> ty_rec:function_keys(V) -- maps:keys(AllFunctions) ++ AccIn; _ -> AccIn end end, [], SubstituteMap),
  % Keys = [function_keys(V) || K := V <- SubstituteMap, lists:member(K, AllVars)],
  OtherFunctionKeys = lists:usort(lists:flatten(Keys)),
  NewDefaultOtherFunctions = maps:from_list([{Length, dnf_var_ty_function:substitute(DefaultFunction, SubstituteMap, Memo, fun(Ty) -> ty_rec:pi({function, Length}, Ty) end)} || Length <- OtherFunctionKeys]),
  AllKeys = maps:keys(AllFunctions) ++ maps:keys(NewDefaultOtherFunctions),

  NewOtherFunctions = maps:from_list(lists:map(fun(Key) ->
    {Key, case maps:is_key(Key, AllFunctions) of
            true -> dnf_var_ty_function:substitute(maps:get(Key, AllFunctions), SubstituteMap, Memo, fun(Ty) -> ty_rec:pi({function, Key}, Ty) end);
            _ -> maps:get(Key, NewDefaultOtherFunctions, NewDefaultFunction)
          end}
                                            end, AllKeys)),

  {NewDefaultFunction, NewOtherFunctions}.

all_variables({Default, Others}, M) when is_map(Others) ->
  lists:usort(lists:flatten(
    dnf_var_ty_function:all_variables(Default, M) ++
    lists:map(fun({_K,V}) -> dnf_var_ty_function:all_variables(V, M) end, maps:to_list(Others))
  ));
all_variables(Ty, M) -> dnf_var_ty_function:all_variables(Ty, M).

has_ref({DefaultF, AllFunction}, TyRef) ->
  false = dnf_var_ty_function:has_ref(DefaultF, TyRef), % should never happen
  maps:fold(fun(_K,F, All) -> All orelse dnf_var_ty_function:has_ref(F, TyRef) end, false, AllFunction).