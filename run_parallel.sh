#!/usr/bin/env bash
# Run make check and make test in parallel podman containers.
# No args: snapshot the working copy (original behavior).
# With args: each arg is a jj bookmark; snapshot each via git archive.
set -uo pipefail

IMAGE="${IMAGE:-docker.io/library/erlang:28}"
WORKDIR="/workspace"
TARGETS=(check test)

TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

# ── Helpers ──────────────────────────────────────────────────────────────────

safe_name() {
    # Replace / with _ so bookmark names are safe for filenames
    printf '%s' "$1" | tr '/' '_'
}

# ── Argument parsing & validation ────────────────────────────────────────────

declare -a BOOKMARKS=()

if [[ $# -eq 0 ]]; then
    BOOKMARKS=("workcopy")
else
    for bm in "$@"; do
        if ! git rev-parse --verify "$bm" >/dev/null 2>&1; then
            echo "ERROR: bookmark '$bm' does not resolve to a valid git ref" >&2
            exit 1
        fi
        BOOKMARKS+=("$bm")
    done
fi

# ── Snapshot creation ────────────────────────────────────────────────────────

declare -A TARS

for bm in "${BOOKMARKS[@]}"; do
    safe=$(safe_name "$bm")
    tarfile="$TMPDIR/${safe}.tar"

    if [[ "$bm" == "workcopy" ]]; then
        echo "==> Creating snapshot of working copy..."
        tar cf "$tarfile" --exclude='.git' --exclude='.jj' --exclude='_build' --exclude='_etylizer' .
    else
        echo "==> Creating snapshot of bookmark '$bm'..."
        git archive --format=tar "$bm" > "$tarfile"
    fi

    TAR_SIZE=$(du -h "$tarfile" | cut -f1)
    echo "    Snapshot: $TAR_SIZE"
    TARS["$bm"]="$tarfile"
done

echo "    Image:    $IMAGE"
echo ""

# ── Pull image ───────────────────────────────────────────────────────────────

echo "==> Pulling image (if needed)..."
podman pull -q "$IMAGE" || true
echo ""

# ── Launch containers ────────────────────────────────────────────────────────

declare -A PIDS LOGS RCS

echo "==> Starting containers..."

for bm in "${BOOKMARKS[@]}"; do
    tarfile="${TARS[$bm]}"
    for target in "${TARGETS[@]}"; do
        key="${bm}:${target}"
        safe=$(safe_name "$bm")
        logfile="$TMPDIR/${safe}_${target}.log"
        LOGS["$key"]="$logfile"

        podman run --rm -i "$IMAGE" \
            sh -c "mkdir -p $WORKDIR && cd $WORKDIR && tar xf - && make build && make $target" \
            < "$tarfile" > "$logfile" 2>&1 &
        PIDS["$key"]=$!

        echo "    $key: PID ${PIDS[$key]}"
    done
done

echo ""
echo "==> Waiting for all containers to finish..."

# ── Wait and collect ─────────────────────────────────────────────────────────

for key in "${!PIDS[@]}"; do
    rc=0
    wait "${PIDS[$key]}" || rc=$?
    RCS["$key"]=$rc
done

# ── Output display ───────────────────────────────────────────────────────────

for bm in "${BOOKMARKS[@]}"; do
    for target in "${TARGETS[@]}"; do
        key="${bm}:${target}"
        rc="${RCS[$key]}"

        echo ""
        echo "========================================"
        echo "  $key (exit code: $rc)"
        echo "========================================"
        cat "${LOGS[$key]}"
    done
done

# ── Summary table ────────────────────────────────────────────────────────────

echo ""
echo "========================================"
echo "  Summary"
echo "========================================"
echo ""

# Determine column width from longest bookmark name (min 10)
max_bm=10
for bm in "${BOOKMARKS[@]}"; do
    (( ${#bm} > max_bm )) && max_bm=${#bm}
done

printf "%-${max_bm}s  %-16s  %-16s\n" "Bookmark" "make check" "make test"
printf "%$(( max_bm + 36 ))s\n" | tr ' ' '-'

all_passed=true
for bm in "${BOOKMARKS[@]}"; do
    row=""
    for target in "${TARGETS[@]}"; do
        key="${bm}:${target}"
        rc="${RCS[$key]}"
        if [[ "$rc" -eq 0 ]]; then
            cell="PASSED"
        else
            cell="FAILED ($rc)"
            all_passed=false
        fi
        row+="$(printf '  %-16s' "$cell")"
    done
    printf "%-${max_bm}s%s\n" "$bm" "$row"
done

echo ""

if $all_passed; then
    exit 0
else
    exit 1
fi
