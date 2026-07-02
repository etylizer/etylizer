#!/usr/bin/env bash
# metrics_matrix.sh — 2x2 engine x corpus metrics matrix for CI.
#
# Inputs are two already-checked-out, already-built trees: a `base` tree and a
# `pr` tree, each with _build/metrics/bin/etylizer built (rebar3 as metrics
# escriptize). We run every suite's corpus through BOTH engines so the report
# can separate the ENGINE effect (hold corpus fixed, vary engine) from the
# SOURCE effect (hold engine fixed, vary corpus), instead of only the
# confounded diagonal (PR/PR vs base/base) the old report showed.
#
# Holding the corpus identical makes ety_metrics_report's name-based "common"
# set exact, so the engine-effect columns are pure verdict/time flips with no
# added/removed-function noise — no hashing or dependency tracking needed.
#
#   A = base, B = PR.   Cells: <suite>_c{A,B}_e{A,B}.json   (corpus, engine)
#
#   run    <base_dir> <pr_dir> <suite> <out_dir>   write the 4 cell JSONs
#   report <suite> <dir> <title>                   print markdown tables
#
# "Engine" = a tree's built escript + its --type-overlay + stdtypes.
# "Corpus" = a tree's -S source + -I headers. Slow functions are not skipped;
# they record as `timeout` at --report-timeout.
set -euo pipefail

SELF_DIR="$(cd "$(dirname "$0")" && pwd)"      # where ety_metrics_report lives
REPORT_TIMEOUT="${REPORT_TIMEOUT:-4000}"

suite_sdir() { case "$1" in
  etylizer)     echo "src" ;;
  typecheck)    echo "test_files/tycheck_simple" ;;
  *) echo "metrics_matrix: unknown suite '$1'" >&2; exit 2 ;;
esac; }

INCLUDES="-I include -I src -I src/erlang_types -I src/erlang_types/dnf"

# cell <corpus_dir> <engine_dir> <suite> <out_json>
cell() {
  local cdir="$1" edir="$2" suite="$3" out="$4"
  local sdir; sdir="$(suite_sdir "$suite")"
  if [ ! -x "$edir/_build/metrics/bin/etylizer" ]; then
    echo "metrics_matrix: no engine at $edir/_build/metrics/bin/etylizer — skipping cell" >&2
    return 0
  fi
  # shellcheck disable=SC2086
  ( cd "$cdir" && "$edir/_build/metrics/bin/etylizer" \
      -P . -S "$sdir" $INCLUDES \
      --type-overlay "$edir/overlays/etylizer_overlay.erl" \
      -f --report-mode report --report-timeout "$REPORT_TIMEOUT" \
      --metrics-file "$out" --no-deps ) \
    || echo "metrics_matrix: cell corpus=$(basename "$cdir") engine=$(basename "$edir") exited nonzero (metrics flushed)" >&2
}

cmd_run() {
  local base pr suite out
  base="$(cd "$1" && pwd)"; pr="$(cd "$2" && pwd)"; suite="$3"
  mkdir -p "$4"; out="$(cd "$4" && pwd)"
  cell "$base" "$base" "$suite" "$out/${suite}_cA_eA.json"   # base corpus, base engine
  cell "$base" "$pr"   "$suite" "$out/${suite}_cA_eB.json"   # base corpus, PR engine
  cell "$pr"   "$base" "$suite" "$out/${suite}_cB_eA.json"   # PR   corpus, base engine
  cell "$pr"   "$pr"   "$suite" "$out/${suite}_cB_eB.json"   # PR   corpus, PR engine
}

cmd_report() {
  local suite="$1" d="$2" t="$3"
  local AeA="$d/${suite}_cA_eA.json" AeB="$d/${suite}_cA_eB.json"
  local BeA="$d/${suite}_cB_eA.json" BeB="$d/${suite}_cB_eB.json"
  local R="$SELF_DIR/ety_metrics_report"
  # Each table holds the SOURCE (corpus) fixed and compares PR engine vs base
  # engine, so every delta is attributable to the engine alone (identical
  # function set). The [..] prefix rides through --title onto every heading.
  # [BASE source]: base corpus, PR engine vs base engine.
  if [ -f "$AeB" ] && [ -f "$AeA" ]; then
    "$R" --title "[BASE source] $t" "$AeB" "$AeA"; echo
  fi
  # [PR source]: PR corpus, PR engine vs base engine.
  if [ -f "$BeB" ] && [ -f "$BeA" ]; then
    "$R" --title "[PR source] $t" "$BeB" "$BeA"; echo
  fi
}

case "${1:-}" in
  run)    shift; cmd_run "$@" ;;
  report) shift; cmd_report "$@" ;;
  *) echo "usage: metrics_matrix.sh run <base_dir> <pr_dir> <suite> <out_dir>" >&2
     echo "       metrics_matrix.sh report <suite> <dir> <title>" >&2
     exit 2 ;;
esac
