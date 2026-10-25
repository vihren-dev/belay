# Status: guide SQL-source rebuild correction

Created 2026-10-24. Status: DONE. Published in private product PR #8.
Task: [task file](20261024-guide-sql-rebuilds.task.md).
Spec: ADR17 D6; accepted owner decision of 2026-10-24.

## Progress

- 2026-10-24: the S7 source/native audit established the expression-column-name
  counterexample. The owner accepted exact metadata and native Lake tracking.
  Specified the bounded private-guide correction and unchanged-SQL validation.
  Await independent task review and assignment after current S4 guide work.
- 2026-10-24: task review `20261024T142048Z-e614f5b6` was clean. The private
  correction `26996a12` passed independent review; its native validation used
  the pinned SQLite 3.51.0 artifact and confirmed equal values with distinct
  expression-column names. All fenced SQL bodies are unchanged. Exact commands,
  native output and review records remain private. Published with the reviewed
  S4 explanatory corrections in private product PR #8 at `e1e42351`.
  This completes the bounded wording task, not the S7 implementation.
