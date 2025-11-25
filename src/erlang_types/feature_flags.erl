-module(feature_flags).

-export_type([report_mode/0, exhaustiveness_mode/0]).

-type report_mode() :: early_exit | report.
-type exhaustiveness_mode() :: enabled | disabled.
