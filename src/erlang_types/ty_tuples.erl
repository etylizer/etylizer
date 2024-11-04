-module(ty_tuples).

-export([compare/2, equal/2, hash/1]).

equal({DefaultT1, T1}, {DefaultT2, T2}) -> 
  % TODO test case: 
  %      we could filter here equivalent representations with left-over
  %      empty and any tuples, e.q. {0, #{1 => Empty}} =:= {0, #{}}
  dnf_var_ty_tuple:equal(DefaultT1, DefaultT2) andalso maps:size(T1) =:= maps:size(T2) andalso
  % TODO minor improvement: stop iterate over all sizes after false is encountered
  maps:map(fun(Size, T, Res) -> Res andalso dnf_var_ty_tuple:equal(T, maps:get(Size, T2)) end, true, T1).

compare(_, _) -> error(todo). % TODO
hash(_) -> 17. % TODO