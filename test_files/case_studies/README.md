# Case studies

`case_studies` holds vendored code that etylizer checks as a metrics suite. 
A manifest per study (`*.study`) lists its modules and, one per
line, everything the check needs from outside:

* a function that is expected to fail or needs a check switched off
* assertions injected from outside similar to how they would in the source
* the `overlays` of a module

A manifest is executable: `./jsone.study` runs the study with the etylizer of this tree, which
has to be built already (`rebar3 as metrics escriptize`). On a terminal it ends with the tables
of `ety_metrics_report`, redirected it prints the metrics as JSON, like `make case-study`.
Every manifest starts with the same `#!` line, the runner does not read one without it.
The log, the metrics and the engine cache of every module stay in `_build/case_study/<study>`.
