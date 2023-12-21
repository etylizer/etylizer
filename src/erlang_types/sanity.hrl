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


-endif.
