-ifndef(SANITY_HRL).
-define(SANITY_HRL,true).

-include_lib("../log.hrl").

-define(LOG_THRESHOLD_MS, 10).
-define(REPORT_THRESHOLD_MS, 100).

-ifdef(debug).
-define(SANITY(Name, X), (fun() -> __Start = erlang:system_time(), X, __Time = (erlang:system_time() - __Start)/1000000, case __Time > ?LOG_THRESHOLD_MS of true -> ?LOG_TRACE("Sanity ~p finished in ~.1f ms", Name, __Time); _ -> ok end end)()).
-define(TIME(Name, X), (fun() -> __Start = erlang:system_time(), __Res = X, __Time = (erlang:system_time() - __Start)/1000000, case {__Time > ?REPORT_THRESHOLD_MS, __Time > ?LOG_THRESHOLD_MS} of {true, _} -> ?LOG_INFO("~p finished in ~.1f ms", Name, __Time); {_, true} -> ?LOG_TRACE("~p finished in ~.1f ms", Name, __Time); _ -> ok end, __Res end)()).
-else.
-define(SANITY(Name, X), ok).
-define(TIME(Name, X), X).
-endif.

-ifdef(debug). % etally sanity checks

-compile({nowarn_unused_function, sanity_substitution/3}).
sanity_substitution({Var, _To}, Ty, TyAfter) ->
  case lists:member(Var, ty_rec:all_variables(Ty)) of
    false ->  ok;
    true ->
      case lists:member(Var, ty_rec:all_variables(TyAfter)) of
        false -> ok;
        _ ->
          error({failed_sanity, Var, variable_is_still_in_ty_after_substitution, {before, ty_rec:print(Ty)}, {'after', ty_rec:print(TyAfter)}})
      end
  end.


%substitution_check sanity check
-compile({nowarn_unused_function, is_valid_substitution/2}).
is_valid_substitution([], _) -> true;
is_valid_substitution([{Left, Right} | Cs], Substitution) ->
  SubstitutedLeft = ty_rec:substitute(Left, Substitution),
  SubstitutedRight = ty_rec:substitute(Right, Substitution),
  Res = ty_rec:is_subtype(SubstitutedLeft, SubstitutedRight) ,
  case Res of
    false ->
      io:format(user, "Left: ~s -> ~s~n", [ty_rec:print(Left), ty_rec:print(SubstitutedLeft)]),
      io:format(user, "Right: ~s -> ~s~n", [ty_rec:print(Right), ty_rec:print(SubstitutedRight)]);
    _ -> ok
  end,
  Res andalso
    is_valid_substitution(Cs, Substitution).

-endif.


-endif.
