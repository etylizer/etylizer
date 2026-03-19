#!/bin/bash
# Generates a markdown table of polymorphic variable statistics from tally logs.
# Parses [tally_poly_vars] N lines emitted by tally.erl when --tally-stats is enabled.
#
# Usage: poly_vars_stats.sh <label> <pr_log> <base_log> [<label> <pr_log> <base_log> ...]
#   Arguments come in triples. base_log can be "" if no base exists.

set -euo pipefail

# Parse [tally_poly_vars] N lines from a log file.
# Sets: ${pfx}_COUNT, ${pfx}_TOTAL, ${pfx}_MIN, ${pfx}_MAX
parse_poly_vars() {
    local file="$1"
    local pfx="$2"

    local count=0 total=0 min=-1 max=0

    if [ -n "$file" ] && [ -f "$file" ]; then
        while IFS= read -r line; do
            if [[ "$line" =~ \[tally_poly_vars\]\ ([0-9]+) ]]; then
                local n="${BASH_REMATCH[1]}"
                count=$((count + 1))
                total=$((total + n))
                if [ "$n" -gt "$max" ]; then max=$n; fi
                if [ "$min" -lt 0 ] || [ "$n" -lt "$min" ]; then min=$n; fi
            fi
        done < "$file"
    fi

    if [ "$min" -lt 0 ]; then min=0; fi

    printf -v "${pfx}_COUNT" '%s' "$count"
    printf -v "${pfx}_TOTAL" '%s' "$total"
    printf -v "${pfx}_MIN"   '%s' "$min"
    printf -v "${pfx}_MAX"   '%s' "$max"
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

fmt_avg_delta() {
    local pr_total=$1 pr_count=$2 base_total=$3 base_count=$4
    local pr_x10=0 base_x10=0
    if [ "$pr_count" -gt 0 ]; then pr_x10=$((pr_total * 10 / pr_count)); fi
    if [ "$base_count" -gt 0 ]; then base_x10=$((base_total * 10 / base_count)); fi
    local da=$((pr_x10 - base_x10))
    local sign=""
    if [ "$da" -gt 0 ]; then sign="+"; fi
    echo "${sign}$((da / 10)).$((${da#-} % 10))"
}

args=("$@")
num_args=${#args[@]}

if [ "$((num_args % 3))" -ne 0 ] || [ "$num_args" -eq 0 ]; then
    echo "Usage: poly_vars_stats.sh <label> <pr_log> <base_log> [...]" >&2
    exit 1
fi

num_rows=$((num_args / 3))

# Always show PR vs Base comparison (missing base files compare against 0)
echo "| Suite | Invocations | | Total vars | | Avg vars | | Min vars | | Max vars | |"
echo "|-------|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"
echo "| | PR | Base | PR | Base | PR | Base | PR | Base | PR | Base |"

for ((i=0; i<num_rows; i++)); do
    label="${args[$((i*3))]}"
    pr_log="${args[$((i*3+1))]}"
    base_log="${args[$((i*3+2))]}"

    parse_poly_vars "$pr_log" "PR"
    pr_avg=$(fmt_avg "$PR_TOTAL" "$PR_COUNT")

    parse_poly_vars "$base_log" "BASE"
    base_avg=$(fmt_avg "$BASE_TOTAL" "$BASE_COUNT")

    echo "| **$label** | $PR_COUNT | $BASE_COUNT | $PR_TOTAL | $BASE_TOTAL | $pr_avg | $base_avg | $PR_MIN | $BASE_MIN | $PR_MAX | $BASE_MAX |"
done

# Print delta row
echo "| | | | | | | | | | | |"
echo "| **Suite** | **Delta** | | **Delta** | | **Delta** | | **Delta** | | **Delta** | |"

for ((i=0; i<num_rows; i++)); do
    label="${args[$((i*3))]}"
    pr_log="${args[$((i*3+1))]}"
    base_log="${args[$((i*3+2))]}"

    parse_poly_vars "$pr_log" "PR"
    parse_poly_vars "$base_log" "BASE"

    d_count=$(fmt_delta "$PR_COUNT" "$BASE_COUNT")
    d_total=$(fmt_delta "$PR_TOTAL" "$BASE_TOTAL")
    d_avg=$(fmt_avg_delta "$PR_TOTAL" "$PR_COUNT" "$BASE_TOTAL" "$BASE_COUNT")
    d_min=$(fmt_delta "$PR_MIN" "$BASE_MIN")
    d_max=$(fmt_delta "$PR_MAX" "$BASE_MAX")

    echo "| **$label** | $d_count | | $d_total | | $d_avg | | $d_min | | $d_max | |"
done
