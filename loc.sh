#!/bin/bash
# Count lines of code
set -euo pipefail

DIR="${1:-./src/erlang_types}"

find "$DIR" -type f \( -name '*.erl' -o -name '*.hrl' \) -print0 \
    | xargs -0 wc -l \
    | tail -n 1 \
    | awk '{print $1}'
