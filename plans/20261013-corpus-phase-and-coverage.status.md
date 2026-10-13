# Status: error phase in corpus records and the resolution coverage corpus, step 2b of ADR 0008

Created 2026-10-13. Status: IN PROGRESS.
Task: [task](20261013-corpus-phase-and-coverage.task.md).
Specification: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md).
Previous step: [step 2a status](20261013-measured-profile-limits.status.md).

Relevant files: `conformance/native_statements.py`, `conformance/native_record.py`,
`conformance/predict.py`, `conformance/native_replay.py`,
`conformance/freeze_corpus.py`, `conformance/corpus_shards.py`,
`conformance/authored_cases.py`,
`packages/verifier-conformance/VerifierConformance/Predict.lean`,
`judge/catalog.py`, `judge/compare.py`, `judge/claims.json`.

## Findings

- Survey, 2026-10-13: corpus events have no phase; `nativeVersion` is 1 to 4;
  the freezer and the shard writer fix version 4 and corpus version 5; the judge
  compares visible, persisted, transaction state and primary code per step and
  ignores other keys; prediction and replay refuse every version 4 record.

## Progress

- 2026-10-13: task and status files created from `main` `69bd75b4`.

## Remaining

- All outcome items of the task.
