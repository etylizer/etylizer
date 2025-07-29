-ifndef(SANITY_HRL).
-define(SANITY_HRL,true).

-include("log.hrl").

-define(LOG_THRESHOLD_MS, 10).
-define(REPORT_THRESHOLD_MS, 100).

-ifdef(ety_debug).
-define(SANITY(Name, X), (fun() -> __Start = erlang:system_time(), X, __Time = (erlang:system_time() - __Start)/1000000, case __Time > ?LOG_THRESHOLD_MS of true -> ?LOG_TRACE("Sanity ~p finished in ~.1f ms", Name, __Time); _ -> ok end end)()).
-define(TIME(Name, X), (fun() -> __Start = erlang:system_time(), __Res = X, __Time = (erlang:system_time() - __Start)/1000000, case {__Time > ?REPORT_THRESHOLD_MS, __Time > ?LOG_THRESHOLD_MS} of {true, _} -> ?LOG_INFO("~p finished in ~.1f ms", Name, __Time); {_, true} -> ?LOG_TRACE("~p finished in ~.1f ms", Name, __Time); _ -> ok end, __Res end)()).
-else.
-define(SANITY(Name, X), ok).
-define(TIME(Name, X), X).
-endif.

-ifdef(ety_debug). % etally sanity checks

-compile({nowarn_unused_function, sanity_substitution/3}).
sanity_substitution({Var, _To}, Ty, TyAfter) ->
  case sets:is_element(Var, ty:all_variables(Ty)) of
    false ->  ok;
    true ->
      case sets:is_element(Var, ty:all_variables(TyAfter)) of
        false -> ok;
        _ ->
          io:format(user,"~nBefore:~n~s~n", [pretty:render_ty(ty_parser:unparse(Ty))]),
          io:format(user,"~nVar:~n~p~n", [Var]),
          io:format(user,"~nTo:~n~s~n", [pretty:render_ty(ty_parser:unparse(_To))]),
          io:format(user,"~nAfter:~n~s~n", [pretty:render_ty(ty_parser:unparse(TyAfter))]),
          error({failed_sanity, Var, variable_is_still_in_ty_after_substitution, {before, ty_node:dumpp(Ty)}, {'after', ty_node:dumpp(TyAfter)}})
      end
  end.


%substitution_check sanity check
-compile({nowarn_unused_function, is_valid_substitution/3}).
is_valid_substitution([], _, _) -> true;
is_valid_substitution([{Left, Right} | Cs], Substitution, MonomorphicVariables) ->

  SubstitutedLeft = ty_node:substitute(Left, Substitution),
  SubstitutedRight = ty_node:substitute(Right, Substitution),
  Res = etally:is_tally_satisfiable([{SubstitutedLeft, SubstitutedRight}], MonomorphicVariables),
  case Res of
    false ->
      P = fun(Ty) -> pretty:render_ty(ty_parser:unparse(Ty)) end,
      io:format(user, "Subst:~n~p~n", [Substitution]),
      io:format(user, "Left:~n~s~n->~n~s~n", [P(Left), P(SubstitutedLeft)]),
      io:format(user, "Right:~n~s~n->~n~s~n", [P(Right), P(SubstitutedRight)]);
    _ -> ok
  end,
  Res andalso
    is_valid_substitution(Cs, Substitution, MonomorphicVariables).

-endif.


-endif.
