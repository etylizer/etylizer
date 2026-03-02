-module(feature_flags).

-export_type([report_mode/0, exhaustiveness_mode/0, gradual_typing_mode/0, dump_tally_constraints/0]).

-type report_mode() :: early_exit | report.
-type exhaustiveness_mode() :: enabled | disabled.
-type gradual_typing_mode() :: dynamic | infer.
-type dump_tally_constraints() :: none | raw | simplified.
