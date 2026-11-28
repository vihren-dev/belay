#!/usr/bin/env bash
# Run the native probes with the given sqlite3 and compare the output with the recorded one.
# The probes show what one pinned SQLite build does; they are evidence for the ADR of query
# results as bags, not a test of SQLite. Probes P15 and P16 end with a runtime error and the
# shell continues, so sqlite3 must exit with status 1. Any other status, for example 124 for
# the deadline or a status above 128 for a crash, fails the run before the comparison.
set -euo pipefail
here=$(dirname "$0")
sqlite=${1:-sqlite3}
expected_status=1
# The deadline for sqlite3; the probes take less than one second.
sqlite_deadline_seconds=60
actual=$(mktemp)
trap 'rm -f "$actual"' EXIT
status=0
timeout "$sqlite_deadline_seconds" "$sqlite" :memory: < "$here/probes.sql" > "$actual" 2>&1 || status=$?
if [ "$status" -ne "$expected_status" ]; then
  echo "run-probes: sqlite3 exited with status $status, expected $expected_status;" \
    "see the output below and check the probes for a hang or a crash." >&2
  cat "$actual" >&2
  exit 1
fi
diff -u "$here/probes.expected" "$actual"
