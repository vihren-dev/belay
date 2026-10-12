# Review log conversion status

Created 2026-10-11. Status: DONE ([PR #87](https://github.com/vihren-dev/sqlite-verifier/pull/87) and the conversion-rule removal).
Task: [20261011-review-log-conversion.task.md](20261011-review-log-conversion.task.md).

## References

- Previous step: `plans/20261011-review-log-per-record-files.task.md`.
- Sources: `tools/review_records.py`, `tools/review_log_check.py`,
  `tools/review_log_frozen.py`, `tests/ci_scope.py`, `justfile`, `AGENTS.md`,
  `docs/ci.md`.

## Progress

- 2026-10-11: task and status files created. Dry run: 590 lines, 556
  distinct records, 0 path collisions, 0 invalid records.
- 2026-10-11: code reads and writes only record files; the check accepts the
  deletion of `reviews/log.jsonl` when each of its records is a file;
  `just review-log-frozen` removed; docs and tests updated (49 review tests).
- 2026-10-11: review finding (code without the conversion leaves records
  unread) fixed: the conversion is in the same commit. 556 distinct records
  written, none missing; `reviews/log.jsonl` deleted; the `review-stats`
  table equals the table of the deduplicated old log plus the existing record
  files; it now counts 325 reviews instead of 346 (21 duplicates). The CI
  check passes against `main`.
- 2026-10-11: last review clean. DONE.
- 2026-10-11: #87 merged. Follow-up: the check no longer has the conversion rule; no code or test names `reviews/log.jsonl`.
