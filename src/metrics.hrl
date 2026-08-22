-ifndef(METRICS_HRL).
-define(METRICS_HRL, true).

-ifdef(ety_metrics).
-define(METRIC(Category, Expr), metrics:record(Category, Expr)).
-define(METRIC_SET_FUN(Label), erlang:put(ety_cur_fun, Label)).
-define(METRIC_GET_FUN(), erlang:get(ety_cur_fun)).
-define(METRIC_FUN(), metrics:current_fun()).
-define(METRIC_INFER_FUN(FileName), metrics:inference_fun(FileName)).
%% Evaluate Expr only in metric builds. Used when the work itself
%% (iteration, multi-statement recording) must vanish without metrics.
-define(METRIC_DO(Expr), Expr).
-else.
-define(METRIC(Category, Expr), ok).
-define(METRIC_SET_FUN(Label), ok).
-define(METRIC_GET_FUN(), undefined).
-define(METRIC_FUN(), '__no_fun__').
-define(METRIC_INFER_FUN(_FileName), '__no_fun__').
-define(METRIC_DO(_Expr), ok).
-endif.

-endif.
