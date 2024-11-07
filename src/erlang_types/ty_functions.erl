-module(ty_functions).

-export([union/2, compare/2, equal/2, hash/1, empty/0, any/0]).

equal({DefaultT1, T1}, {DefaultT2, T2}) ->
  % TODO see comments in ty_tuples
  dnf_var_ty_function:equal(DefaultT1, DefaultT2) andalso maps:size(T1) =:= maps:size(T2) andalso
  maps:fold(fun(Size, T, Res) -> Res andalso dnf_var_ty_function:equal(T, maps:get(Size, T2)) end, true, T1).

compare(_, _) -> error(todo). % TODO
hash(_) -> 17. % TODO

empty() ->
  {dnf_var_ty_function:empty(), #{}}.

any() ->
  {dnf_var_ty_function:any(), #{}}.

union({DefaultF1, F1}, {DefaultF2, F2}) ->
  % get all keys
  AllKeys = maps:keys(F1) ++ maps:keys(F2),
  UnionKey = fun(Key) ->
    dnf_var_ty_function:union(
      maps:get(Key, F1, DefaultF1),
      maps:get(Key, F2, DefaultF2)
    )
                 end,
  {dnf_var_ty_function:union(DefaultF1, DefaultF2), maps:from_list([{Key, UnionKey(Key)} || Key <- AllKeys])}.