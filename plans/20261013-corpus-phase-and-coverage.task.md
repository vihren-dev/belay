# Error phase in corpus records and the resolution coverage corpus, step 2b of ADR 0008

Created 2026-10-13. Status: IN PROGRESS.
Specification: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md),
"How `resolve` is tested" (error phase, coverage rule, limits) and "Execution
profile" (frozen records); ADR 0011 for the judge and its claims. Previous step:
[step 2a](20261013-measured-profile-limits.task.md), DONE.

## Plan of step 2b

Two pull requests, so that the judge pull request can claim agreement at once:

- **Pull request A (subject):** the recorder, the record format, the prediction
  path, replay, the authored coverage definitions and the freeze tooling for a
  new corpus. No file under `judge/` or `integrity/` changes, and no corpus
  directory is added.
- **Pull request B (judge, owner approval):** the judge compares the error
  phase; the coverage corpus is frozen as a new claimed corpus with a
  `mustAgree` claim for each agreeing case; the lock is updated.

## Outcome

1. **Native record version 5.** A corpus record of version 5 is version 4
   (outputs, explicit profile) with a profile of format 3 (measured limits),
   and a `phase` (`prepare`, `step` or `null`) in each trace event. A fixture
   may lower limits. Versions 1 to 4 are unchanged and stay readable.
2. **Prediction and replay of profiled records.** The prediction input and
   `Predict.lean` take the recorded profile (release, source id, limits,
   double-quoted-string settings) instead of `Profile.documented`; each
   predicted step carries the model's error phase. A record whose profile has
   execution settings the model does not implement (foreign keys, recursive
   triggers, IMMEDIATE transactions, a controlled clock, read-only access) stays
   out of scope, with that reason. Replay (`native_replay.model_case`) follows
   the same rule and copies the recorded phase into the model case. The effect
   on the verdicts of the claimed corpora is measured; no claimed case may
   change from AGREE, and none may become DISAGREE or HARNESS_ERROR.
3. **Coverage definitions.** Authored cases cover each condition of each
   first-scope resolution rule with a case where it applies, a neighbor where
   it just does not apply, and cases where two errors apply at once. They
   include the prepare-error conditions that step 2a left without a model case
   (reserved names, multiple primary keys, non-constant defaults, altering a
   schema table, INSERT and UPDATE column errors, CREATE TABLE column checks),
   and limit cases under lowered limits with one at the default value. Each case
   names the requirement identifiers it covers.
4. **Freeze tooling.** The freezer and the shard writer can write a new corpus
   version with records of version 5; corpus-v5 stays readable and unchanged.
5. **Judge (pull request B).** `judge/` compares `phase` when a recorded step
   has one; the frozen coverage corpus is claimed; `integrity/judge.lock.json`
   is updated with `just judge-lock`.
6. **Documents.** `docs/native-corpus-format.md`, `docs/conformance-format-v2.md`
   and `docs/execution-profile.md` describe version 5; the judge's document
   describes the phase comparison.

## Tests

- Recorder: a version 5 record has the measured limits and a phase on each
  failed event, for a prepare error and a step error.
- Prediction: a version 5 record is predicted under its limits, with phases; a
  record with an unsupported execution setting is out of scope with a reason.
- Replay: the phase of a version 5 record reaches the model case.
- Coverage: every authored coverage case agrees, compiled; each names at least
  one requirement identifier; the resolve mutants of step 2a stay killed.
- Freeze: a small version 5 corpus is written and read back.
- Judge (pull request B): a prediction with a different phase disagrees; a
  record without phases compares as before; the verdict passes with the new
  claims.
- The existing suites and the verdict pass; the verdict counts of the claimed
  corpora do not go down.

## Key points for the implementer

- `native_statements.py` calls `sqlite3_prepare_v2` and `sqlite3_step` itself
  and catches both as one `NativeError`; it must keep `error.phase`, which
  `native_connection.Connection.check` now sets when given a phase.
- `native_record.record_sql` chooses `nativeVersion` from its options; only
  `authored_cases.records` passes a profile today.
- `freeze_corpus.freeze` requires `nativeVersion == 4` and writes
  `corpus_version=5`; `corpus_shards.FORMATS` fixes `nativeVersion` 4.
  `tests/test_locked_corpora_inventory.py` requires every `conformance/corpus-v*`
  directory to be claimed, so the new corpus directory is created only in pull
  request B.
- The judge ignores keys it does not compare, so pull request A can add the
  phase to predictions before the judge reads it.
- Supporting profiled version 4 records reclassifies corpus-v5 cases. Measure
  before deciding; if a case would disagree, keep version 4 out of scope and
  record the case as a finding.
