# Further JSON functions, slice 6c of ADR 0012: status

Created 2026-10-17. Status: open.
Task: [20261017-json-functions.task.md](20261017-json-functions.task.md).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), Amendment 5, "Further JSON
functions (slice 6c)".

## Relevant files

- JSON port: `packages/belay-sqlite/Belay/Sqlite/Json/` (`Read.lean`, `Extract.lean`,
  `JsonApply.lean`, `Node.lean`).
- Resolution: `Resolution/Calls.lean`, `Resolution/QueryForm.lean` (`JsonFunction`).
- Failures: `JsonFaults.lean`, `JsonReady.lean`.
- Cases: `conformance/authored_json.py` (slice 6b) as the pattern.

## Progress

- 2026-10-17: task and status files, stacked on #145 (slice 6b, PR B). Native facts
  checked on SQLite 3.51.0, one statement per line: the type names; `9223372036854775808`
  and `0x1F` are `integer`, `1e400` `real`; `json_valid` without flags rejects JSON5 and
  comments, flag 2 accepts them, flags 4 and 8 give 0 for text; the flags are the integer
  value of the argument, and 0, NULL, `'x'`, a BLOB and 16 are the flags error;
  `json_array_length` is 0 for an object and a scalar; `json` keeps `1.50e2`, `-0`,
  `1E400` and duplicate keys; wrong argument counts are prepare errors. The escape
  `A` stays as written in rendered JSON text: the ADR's example for slice 6b came
  from the shell, which converts `\uXXXX` in its input, and is corrected.

## Remaining

- Implementation, full checks, review, CI time, pull request A; then pull request B
  (claim corpus 23, `mustAgree`).
