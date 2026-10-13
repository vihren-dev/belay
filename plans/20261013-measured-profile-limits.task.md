# Measured profile limits, error phase and resolve mutants, step 2a of ADR 0008

Created 2026-10-13. Status: DONE (2026-10-13).
Specification: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md),
"Execution profile" (limits, measurement, frozen records) and "How `resolve` is
tested" (error phase, limits, mutants), and the recorder items of "Cleanup after
implementation". Previous step: [step 1b](20261012-resolution-switch.task.md),
DONE.

## Plan of step 2

The owner plan of 2026-10-10 makes step 2 one step: measured profile limits,
the error phase in the case format, the authored coverage shard and the
mutants. Since then ADR 0011 locks the judge, its claims and the claimed
corpora: a change to them needs its own pull request with owner approval.
Step 2 is therefore split (decision of 2026-10-13, under the owner's "do what
you think is best"):

- **Step 2a (this task):** everything on the subject side. The recorder, the
  profile format, the model case format, Lean's use of the recorded profile,
  the authored model cases and the mutants. No file under `judge/` or
  `integrity/` changes, and no claimed corpus changes.
- **Step 2b:** the judge compares the error phase, and the authored coverage
  cases are frozen into a claimed corpus with `mustAgree` claims. One judge
  pull request for the owner, then the work.

## Outcome

1. **Measured limits.** A native connection no longer sets the column limit.
   The recorder reads each limit of the ADR's table with
   `sqlite3_limit(db, id, -1)` and records it. A fixture may ask for lower
   limits; the recorder sets them before the schema runs and records the
   values that the connection reports. The 2,000 constant and its readback
   check in `conformance/native_connection.py` are gone.
2. **Profile format.** The Python `ExecutionProfile` gets a limits field in a
   new profile format version. A profile of an older format has no limits
   field; a reader takes its limits from the `SQLITE_MAX_*` values of its
   recorded compile options, or SQLite's documented default where the option
   is absent. No frozen record changes.
3. **Model case format.** A new case version carries the measured profile
   (release, source id, limits, double-quoted-string settings) and, for each
   observation with an error, its phase: `prepare` when
   `sqlite3_prepare_v2` failed, `step` when `sqlite3_step` failed. Lean
   resolves the case under the recorded profile, not under
   `Profile.documented`. A native prepare error agrees only with a modeled
   `ExecutionError.prepare` at the same position; a native step error agrees
   only with another modeled error.
4. **Authored model cases.** `conformance/model_cases.py` has a native case
   for each first-scope condition that the ADR lists as uncovered: CREATE
   TABLE for a table that exists, a duplicate column in ADD COLUMN, a table
   with the name of an index, more columns than the limit, COMMIT and
   ROLLBACK with no active transaction, and two errors in one statement. Each
   condition has a neighbor case where it just does not apply. The column
   limit cases run under a profile with a lowered column limit, and are
   kernel-proved like the other small cases.
5. **Default-value case.** The ADR asks for one case of each limit at its
   default value. The existing 2,000-column case `limit_before_duplicate`
   stays as that case for the column limit, compiled-only (its kernel proof
   takes more than 120 s). Decision of 2026-10-13, for owner review: the ADR
   also says the suite needs no 2,000-column table, and the two sentences
   conflict for the column limit.
6. **Mutants of `resolve`.** Each mutant of the ADR's list changes the verdict
   of at least one model case: fold non-ASCII letters, change the order of the
   affinity rules, make `INTEGER PRIMARY KEY DESC` a rowid alias, keep the
   catalog after ROLLBACK, permit a table and an index with the same name, use
   2,000 columns instead of the profile limit, and remove each prepare-error
   condition that a model case covers, one at a time. Decision of 2026-10-13,
   for owner review: a mutant counts as killed when a case leaves AGREE, also to
   `MODEL_UNSUPPORTED`, because the model refuses coercing writes and the
   affinity and rowid-alias mutants can only move a case out of scope; the ADR
   says "disagree". The prepare-error conditions without a model case get
   their cases with the authored coverage shard of step 2b.
7. **Documents.** `docs/execution-profile.md`, `docs/conformance-format-v1.md`
   (the model case), `docs/conformance-format-v2.md` (the profile record),
   `docs/conformance-fixtures.md` and `docs/conformance-model.md` describe the
   measured limits, the case version and the error phase.

## Tests

- Recorder: a connection reports the limits that it records; a fixture with
  a lowered column limit records that value; a recorded profile round-trips
  through its wire form; an old-format profile yields the limits of its
  compile options.
- Error phase: a statement that fails in `sqlite3_prepare_v2` and one that
  fails in `sqlite3_step` (for example ADD COLUMN NOT NULL without a default
  on a table with rows, if the model scope admits it, otherwise a constraint
  violation) are recorded with their phases; a case whose phase is changed
  disagrees.
- Model cases: each new case agrees, compiled and kernel-proved (except the
  default-value case, compiled only); a case recorded under a lowered limit
  disagrees when Lean uses the documented defaults instead.
- Mutants: the mutation check reports each mutant of outcome 6 as killed,
  and names the killing case.
- The existing suites, the examples and the verdict job pass. The verdict
  counts do not go down.

## Key points for the implementer

- `native_trace.record` writes model cases; `native_record.record_sql` writes
  corpus records (`nativeVersion` 1-4). Only the corpus path records a full
  profile today. Corpus records of version 4 stay out of the model's scope in
  `conformance/predict.py` and `native_replay.py`; this step does not change
  that, so the judge's input is unchanged.
- Both recorders execute through `Connection` (`_query_result`, and
  `native_statements.py`), which call `sqlite3_prepare_v2` and then
  `sqlite3_step` but raise one `NativeError`. The phase must be kept at the
  point of failure, not derived later from the message.
- `VerifierConformance/Case.lean` and `Predict.lean` call
  `Profile.documented`. `Predict.lean` keeps it, because predictions follow
  the judge's input format.
- `conformance/mutation_check.py` patches copied Lean sources by exact text
  in a private namespace. `Case.lean` calls `resolveSchemaAndScript` from the
  real namespace, so the resolution modules must be copied too, or a resolve
  mutant has no effect.
- Kernel proofs of model cases evaluate `resolve` in the kernel. Keep the
  lowered-limit cases small (a limit of a few columns) so each proof stays
  near the 2 s of the other small cases.
- `tests/conformance_generation_test.py`, `conformance_pipeline_test.py` and
  `conformance_model_test.py` use the 2,000-column fixture. They keep it only
  where it is the default-value case.
- The native library check of the compile option `MAX_COLUMN=2000`
  (`native_library.py`) checks the pinned build and stays.
