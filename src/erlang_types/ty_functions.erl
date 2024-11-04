-module(ty_functions).

-export([compare/2, equal/2, hash/1]).

equal({DefaultT1, T1}, {DefaultT2, T2}) ->
  % TODO see comments in ty_tuples
  dnf_var_ty_function:equal(DefaultT1, DefaultT2) andalso maps:size(T1) =:= maps:size(T2) andalso
  maps:map(fun(Size, T, Res) -> Res andalso dnf_var_ty_function:equal(T, maps:get(Size, T2)) end, true, T1).

compare(_, _) -> error(todo). % TODO
hash(_) -> 17. % TODO