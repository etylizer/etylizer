-module(prop_phi_function_tally).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").
-import(prop_subty, [limited_ast/0]).

% phi should terminate in reasonable amount of time
prop_phi_no_timeout() ->
  ?FORALL({T1, T2, P}, {limited_ast(), limited_ast(), list({limited_ast(), limited_ast()})},
    begin
      PFuns = lists:map(fun({D, C}) -> ty_function:function(D, C) end, lists:sublist(P, 6)),
%%      io:format("~n~p ~p ~p~n", [ty_ref:load(T1), ty_ref:load(T2), PFuns]),
      {_New, _} = timer:tc(fun() -> dnf_ty_function:explore_function_norm(T1, ty_rec:negate(T2), PFuns, sets:new(), sets:new()) end),
%%      io:format(user, "~ndone in ~p~n", [New]),
      true
    end
  ).
