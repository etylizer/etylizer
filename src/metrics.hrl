-ifndef(METRICS_HRL).
-define(METRICS_HRL, true).

-ifdef(ety_metrics).
-define(METRIC(Category, Expr), metrics:record(Category, Expr)).
-else.
-define(METRIC(Category, Expr), ok).
-endif.

-endif.
