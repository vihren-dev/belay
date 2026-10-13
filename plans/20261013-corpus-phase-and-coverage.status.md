# Status: error phase in corpus records and the resolution coverage corpus, step 2b of ADR 0008

Created 2026-10-13. Status: DONE (2026-10-13).
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
- 2026-10-13: native record version 5 (format-3 profile, `phase` per event) and
  prediction and replay of profiled records (`conformance/profile_scope.py`,
  `conformance/record_versions.py`). A profile is in scope when it uses only the
  default execution settings. Verdict on the claimed corpora: corpus-v4 15 AGREE
  (was 0), corpus-v5 70 AGREE (was 0), all other counts unchanged, no DISAGREE or
  HARNESS_ERROR. The authored replay tests now expect 5 and 10 agreements.
  Finding: a subject input has the record's profile but no trace, so
  `record_parser.record_profile` reads it from the wire form. Finding:
  `native_observation` read 2,000 columns at a time; it now uses the
  connection's column limit.
- 2026-10-13: commit `b24c25ac`; review: two should findings, fixed in `414532f9`
  (no findings).
- 2026-10-13: 41 authored coverage cases (`conformance/authored_resolution.py`),
  each with requirement identifiers, recorded as version 5 records; 37 agree with
  phases, 4 are out of scope (a parenthesized default expression; NOT NULL added
  to a table with rows, a step error; CREATE TABLE with a primary key or a
  default). Review `20261013T084407Z-248564ed` asked for neighbors of every
  condition; added. `conformance/resolution_evidence.py` writes
  them as corpus version 6; `corpus_shards.write` takes the record version.
- 2026-10-13: CI time of pull request A against `main` `69bd75b4`, two rounds that
  alternate `main` and the branch, forced rebuilds of the full `tests` set: 239 s
  and 239 s on `main`, 251 s and 252 s on the branch (+13 s, +5%). The verdict's
  prediction step takes 8 s instead of 2 s, because profiled records of corpus-v4
  and corpus-v5 are now parsed and resolved instead of refused at once. Lean
  builds unchanged.

- 2026-10-13: pull request A merged (#104). Pull request B (judge): the judge
  compares the error phase of version 5 records and treats version 5 as a version
  with outputs; `conformance/corpus-v6` freezes the 41 coverage cases; the claims
  add its 37 agreeing cases and the 15 corpus-v4 and 70 corpus-v5 cases that
  agree since #104; the lock is updated. Verdict: corpus-v6 37 AGREE, 4
  MODEL_UNSUPPORTED, all other counts unchanged. Review
  `20261013T115124Z-5a29143a`: no findings.

## Remaining

- Nothing for step 2b. Pull request B needs the owner's approval (ADR 0011).
