#!/usr/bin/env bash
# Run the native probes with the given sqlite3 and compare the output with the recorded one.
# The probes show what one pinned SQLite build does; they are evidence for the ADR of query
# results as bags, not a test of SQLite. Probe P15 ends with an error, so the exit code of
# sqlite3 is not checked; the comparison of the output finds every change.
set -euo pipefail
here=$(dirname "$0")
sqlite=${1:-sqlite3}
actual=$(mktemp)
trap 'rm -f "$actual"' EXIT
timeout 60 "$sqlite" :memory: < "$here/probes.sql" > "$actual" 2>&1 || true
diff -u "$here/probes.expected" "$actual"
