#!/bin/bash
# Generates markdown statistics tables from typecheck/test log files.
# Usage: typecheck_stats.sh <pr_log> [base_log] [output_file]
#   pr_log:      Log file from a typecheck or test run on the PR branch
#   base_log:    Optional log file from the same run on the base branch
#   output_file: Optional file to write the markdown table to

set -euo pipefail

PR_LOG="${1:-}"
BASE_LOG="${2:-}"
OUTPUT_FILE="${3:-}"

if [ -z "$PR_LOG" ] || [ ! -f "$PR_LOG" ]; then
    echo "Usage: typecheck_stats.sh <pr_log> [base_log] [output_file]" >&2
    exit 1
fi

# Detect log format: "typecheck" uses "(NNN ms)", "eunit" uses "[N.NNN s] ok"
detect_format() {
    if grep -q '\[[0-9.]\+ s\]' "$1" 2>/dev/null; then
        echo "eunit"
    else
        echo "typecheck"
    fi
}

FORMAT=$(detect_format "$PR_LOG")

# Parse a typecheck log file and set stats variables with a given prefix
parse_typecheck_log() {
    local file="$1"
    local pfx="$2"

    local total=0 ok=0 errors=0 timeouts=0 sum_ms=0 max_ms=0 min_ms=-1
    local max_func="" min_func=""

    while IFS= read -r line; do
        if [[ "$line" =~ \(([0-9]+)\ ms\) ]]; then
            local ms="${BASH_REMATCH[1]}"
            local func
            func=$(echo "$line" | awk '{print $2}')

            total=$((total + 1))
            sum_ms=$((sum_ms + ms))

            if [ "$ms" -gt "$max_ms" ]; then
                max_ms=$ms
                max_func=$func
            fi
            if [ "$min_ms" -lt 0 ] || [ "$ms" -lt "$min_ms" ]; then
                min_ms=$ms
                min_func=$func
            fi

            case "$line" in
                Ok:*) ok=$((ok + 1)) ;;
                Error:*) errors=$((errors + 1)) ;;
                Timeout:*) timeouts=$((timeouts + 1)) ;;
            esac
        fi
    done < "$file"

    printf -v "${pfx}_TOTAL" '%s' "$total"
    printf -v "${pfx}_OK" '%s' "$ok"
    printf -v "${pfx}_ERRORS" '%s' "$errors"
    printf -v "${pfx}_TIMEOUTS" '%s' "$timeouts"
    printf -v "${pfx}_SUM_MS" '%s' "$sum_ms"
    printf -v "${pfx}_MAX_MS" '%s' "$max_ms"
    printf -v "${pfx}_MIN_MS" '%s' "$min_ms"
    printf -v "${pfx}_MAX_FUNC" '%s' "$max_func"
    printf -v "${pfx}_MIN_FUNC" '%s' "$min_func"
}

# Parse an eunit log file and set stats variables with a given prefix
# Format: ...(test_files/tycheck_simple/file.erl/test_name (typecheck))...[1.234 s] ok
parse_eunit_log() {
    local file="$1"
    local pfx="$2"

    local total=0 ok=0 errors=0 sum_ms=0 max_ms=0 min_ms=-1
    local max_func="" min_func=""

    while IFS= read -r line; do
        if [[ "$line" =~ \[([0-9]+)\.([0-9]+)\ s\]\ (ok|FAILED) ]]; then
            local secs="${BASH_REMATCH[1]}"
            local frac="${BASH_REMATCH[2]}"
            local status="${BASH_REMATCH[3]}"
            # Convert to ms: seconds * 1000 + fraction
            # frac could be 1-3 digits, pad/truncate to 3
            frac="${frac}000"
            frac="${frac:0:3}"
            local ms=$(( secs * 1000 + 10#$frac ))

            # Extract test name from parentheses before the timing
            local func=""
            local re='\((.+)\)\.\.\.\['
            if [[ "$line" =~ $re ]]; then
                func="${BASH_REMATCH[1]}"
                # Shorten: "test_files/tycheck_simple/file.erl/test (mode)" -> "file.erl/test"
                func=$(echo "$func" | sed 's|.*/\([^/]*/[^ ]*\).*|\1|')
            fi

            total=$((total + 1))
            sum_ms=$((sum_ms + ms))

            if [ "$ms" -gt "$max_ms" ]; then
                max_ms=$ms
                max_func=$func
            fi
            if [ "$min_ms" -lt 0 ] || [ "$ms" -lt "$min_ms" ]; then
                min_ms=$ms
                min_func=$func
            fi

            if [ "$status" = "ok" ]; then
                ok=$((ok + 1))
            else
                errors=$((errors + 1))
            fi
        fi
    done < "$file"

    printf -v "${pfx}_TOTAL" '%s' "$total"
    printf -v "${pfx}_OK" '%s' "$ok"
    printf -v "${pfx}_ERRORS" '%s' "$errors"
    printf -v "${pfx}_TIMEOUTS" '%s' "0"
    printf -v "${pfx}_SUM_MS" '%s' "$sum_ms"
    printf -v "${pfx}_MAX_MS" '%s' "$max_ms"
    printf -v "${pfx}_MIN_MS" '%s' "$min_ms"
    printf -v "${pfx}_MAX_FUNC" '%s' "$max_func"
    printf -v "${pfx}_MIN_FUNC" '%s' "$min_func"
}

parse_log() {
    if [ "$FORMAT" = "eunit" ]; then
        parse_eunit_log "$1" "$2"
    else
        parse_typecheck_log "$1" "$2"
    fi
}

fmt_time() {
    local ms=$1
    if [ "$ms" -ge 60000 ]; then
        echo "$((ms / 60000))m $((ms % 60000 / 1000))s"
    elif [ "$ms" -ge 1000 ]; then
        echo "$((ms / 1000)).$((ms % 1000 / 100))s"
    else
        echo "${ms}ms"
    fi
}

fmt_avg() {
    local sum=$1 count=$2
    if [ "$count" -eq 0 ]; then echo "0"; return; fi
    local avg=$((sum * 10 / count))
    echo "$((avg / 10)).$((avg % 10))"
}

fmt_delta() {
    local pr_val=$1 base_val=$2
    local diff=$((pr_val - base_val))
    if [ "$diff" -gt 0 ]; then
        echo "+$diff"
    else
        echo "$diff"
    fi
}

# Parse PR log
parse_log "$PR_LOG" "PR"

if [ "$PR_TOTAL" -eq 0 ]; then
    echo "No timing data found in PR log." >&2
    exit 1
fi

PR_AVG=$(fmt_avg "$PR_SUM_MS" "$PR_TOTAL")
PR_TIME_FMT=$(fmt_time "$PR_SUM_MS")

# Check if we have base data
HAS_BASE=false
if [ -n "$BASE_LOG" ] && [ -f "$BASE_LOG" ]; then
    parse_log "$BASE_LOG" "BASE"
    if [ "$BASE_TOTAL" -gt 0 ]; then
        HAS_BASE=true
        BASE_AVG=$(fmt_avg "$BASE_SUM_MS" "$BASE_TOTAL")
        BASE_TIME_FMT=$(fmt_time "$BASE_SUM_MS")
    fi
fi

# Label for typecheck vs test
if [ "$FORMAT" = "eunit" ]; then
    LABEL="tests"
    LABEL_SINGULAR="test"
else
    LABEL="functions"
    LABEL_SINGULAR="function"
fi

if [ "$HAS_BASE" = true ]; then
    DELTA_TOTAL=$(fmt_delta "$PR_TOTAL" "$BASE_TOTAL")
    DELTA_OK=$(fmt_delta "$PR_OK" "$BASE_OK")
    DELTA_ERRORS=$(fmt_delta "$PR_ERRORS" "$BASE_ERRORS")
    DELTA_TIMEOUTS=$(fmt_delta "$PR_TIMEOUTS" "$BASE_TIMEOUTS")
    DELTA_TIME_MS=$(fmt_delta "$PR_SUM_MS" "$BASE_SUM_MS")
    DELTA_TIME_FMT=$(fmt_time "${DELTA_TIME_MS#[+-]}")
    # Restore sign
    case "$DELTA_TIME_MS" in
        -*) DELTA_TIME_FMT="-$DELTA_TIME_FMT" ;;
        +*) DELTA_TIME_FMT="+$DELTA_TIME_FMT" ;;
        0)  DELTA_TIME_FMT="0" ;;
    esac
    DELTA_MAX=$(fmt_delta "$PR_MAX_MS" "$BASE_MAX_MS")
    DELTA_MIN=$(fmt_delta "$PR_MIN_MS" "$BASE_MIN_MS")

    # Compute avg delta
    PR_AVG_X10=$((PR_SUM_MS * 10 / PR_TOTAL))
    BASE_AVG_X10=$((BASE_SUM_MS * 10 / BASE_TOTAL))
    DELTA_AVG_X10=$((PR_AVG_X10 - BASE_AVG_X10))
    DELTA_AVG_SIGN=""
    if [ "$DELTA_AVG_X10" -gt 0 ]; then DELTA_AVG_SIGN="+"; fi
    DELTA_AVG="${DELTA_AVG_SIGN}$((DELTA_AVG_X10 / 10)).$((${DELTA_AVG_X10#-} % 10))"

    MD="| Metric | PR | Base | Delta |
|--------|----|------|-------|
| Total $LABEL | $PR_TOTAL | $BASE_TOTAL | $DELTA_TOTAL |
| OK | $PR_OK | $BASE_OK | $DELTA_OK |
| Errors | $PR_ERRORS | $BASE_ERRORS | $DELTA_ERRORS |
| Timeouts | $PR_TIMEOUTS | $BASE_TIMEOUTS | $DELTA_TIMEOUTS |
| Total time | $PR_TIME_FMT | $BASE_TIME_FMT | $DELTA_TIME_FMT |
| Avg per $LABEL_SINGULAR | ${PR_AVG}ms | ${BASE_AVG}ms | ${DELTA_AVG}ms |
| Max | ${PR_MAX_MS}ms (\`$PR_MAX_FUNC\`) | ${BASE_MAX_MS}ms (\`$BASE_MAX_FUNC\`) | ${DELTA_MAX}ms |
| Min | ${PR_MIN_MS}ms (\`$PR_MIN_FUNC\`) | ${BASE_MIN_MS}ms (\`$BASE_MIN_FUNC\`) | ${DELTA_MIN}ms |"
else
    MD="| Metric | Value |
|--------|-------|
| Total $LABEL | $PR_TOTAL |
| OK | $PR_OK |
| Errors | $PR_ERRORS |
| Timeouts | $PR_TIMEOUTS |
| Total time | $PR_TIME_FMT |
| Avg per $LABEL_SINGULAR | ${PR_AVG}ms |
| Max | ${PR_MAX_MS}ms (\`$PR_MAX_FUNC\`) |
| Min | ${PR_MIN_MS}ms (\`$PR_MIN_FUNC\`) |"
fi

echo "$MD"

if [ -n "$OUTPUT_FILE" ]; then
    echo "$MD" > "$OUTPUT_FILE"
fi
