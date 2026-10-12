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
%% Increment a per-process counter, see metrics:count/2.
-define(METRIC_COUNT(Via, Kind), metrics:count(Via, Kind)).
-define(METRIC_SUBPROBLEM(Via, Kind), metrics:count(Via, Kind)).
%% Record a type error of the current function with its kind and line.
-define(METRIC_TYPE_ERROR(Kind, Loc), metrics:record_type_error(Kind, Loc)).
-else.
-define(METRIC(Category, Expr), ok).
-define(METRIC_SET_FUN(Label), ok).
-define(METRIC_GET_FUN(), undefined).
-define(METRIC_FUN(), '__no_fun__').
-define(METRIC_INFER_FUN(_FileName), '__no_fun__').
-define(METRIC_DO(_Expr), ok).
-define(METRIC_COUNT(_Via, _Kind), ok).
-define(METRIC_SUBPROBLEM(_Via, _Kind), ok).
-define(METRIC_TYPE_ERROR(_Kind, _Loc), ok).
-endif.

-endif.
