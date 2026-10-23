# Concrete native/model comparisons

ADR 0004's conformance pipeline uses one Lean `classifyCase` function for compiled
comparison and its `checkCase` predicate for kernel proofs. The
[case format](conformance-format-v1.md) includes the statement syntax of the SQL,
the native tables with their PRAGMA metadata, and native initial/per-statement
observations. Lean resolves the syntax, executes it, and compares the catalog and
rows after each statement.

Inside the pinned Nix shell:

```sh
just conformance --repeat 3 --prove
nix-build build-support/default.nix -A tests.model --no-out-link \
  --option sandbox true --option sandbox-fallback false \
  --extra-experimental-features 'nix-command flakes'
```

The first command writes JSON cases, decoded Lean regression terms, and measured
native-plus-compiled throughput to `build/conformance-evidence/`. Kernel proof
time is excluded from the reported throughput. The conformance executable is a
separate test build; it adds no shipped verifier command. `just test-full` includes the
same Nix model target, without executing it twice on the host.

The [review validation report](../reports/20260929-adr4-review-validation.json)
records 15 agreements and 42 native observations in 1.039 seconds on Darwin arm64:
0.755 seconds of native acquisition and 0.284 seconds for one compiled batch,
including JSON transport and process startup (14.44 cases/second end to end).
Proof-term emission and all five kernel checks run outside that timer. This is a
warm five-case DDL workload, not pure evaluator or generator-scale throughput;
Linux was not executed locally. The report includes source hashes and runtime
identities. The [original report](../reports/20260929-adr4-prototype.json) is retained
as historical evidence from before connection, metadata and streaming corrections.

## Preserved authored cases

The cases in `conformance/model_cases.py` (the five original cases and the 11
resolution cases of ADR 0008) keep their independent
fixtures and final expectations. Native results are checked against those
expectations before the same decoded case receives a compiled verdict and a
kernel proof. Their authored native diagnostic substrings and exact modeled
failure categories/positions are also retained, independently of the generic
primary-code comparator. No expected value is derived from the model.

| Derived case | Required independent observation |
| --- | --- |
| ADD then CREATE | All three old rowids and integer/text/NULL cells survive; appended cells are NULL; audit table is empty. |
| ADD then conflicting CREATE | ADD remains committed; later table creation is not reached. |
| CREATE then duplicate-column ADD | New audit table remains committed; old invoices remain unchanged. |
| CREATE then missing-table ADD | New audit table remains committed; missing-table error occurs at statement 1. |
| ADD at 2000 columns with a duplicate name | Column-limit error takes precedence over duplicate-column error; all columns and empty contents remain. Compiled only: the default-value case of the column limit. |
| CREATE with an ASCII case variant of an existing name | Table-exists error; SQLite folds only ASCII letters. |
| CREATE with a non-ASCII variant of an existing name | Succeeds: the neighbor of the case above. |
| CREATE with the name of an index | Index-name error; the table and its index remain. |
| COMMIT, ROLLBACK without a transaction | No-active-transaction error at statement 0, reported by `sqlite3_step`. |
| BEGIN, ADD, ROLLBACK | The catalog and the rows return to the state at BEGIN. |
| ADD under a column limit of 5 | Reaching the limit succeeds; one column more fails; the limit error takes precedence over a duplicate name. The recorder lowers the limit and records it. |
| INSERT under a unique key on a `CHARINT` column | Succeeds: the INTEGER affinity rule comes before the TEXT rule, so the key is integer-comparable. |
| INSERT into a table with `INTEGER PRIMARY KEY DESC` | Succeeds with row id 1: a descending key is not a rowid alias. |

All fixtures survive JSON decoding unchanged, including rowids `-4`, `9`,
`22`, NULL, UTF-8 text and the 2000-column table. Their former separate model
assertions were replaced only after native replay through the persistent runner
agreed. The lost-row negative check now rejects a proof of the shared predicate.
Imported `alter3` fixtures and their expectations are unchanged.

`conformance/resolve_mutants.py` checks that these cases test each rule of name
resolution (ADR 0008). Each mutant is a copy of the `belay-sqlite-model` and
`verifier-conformance` packages with one change, such as folding non-ASCII
letters, keeping the catalog after ROLLBACK, a constant column limit of 2,000, or
one removed prepare-error condition. Lake builds only the import closure of
`VerifierConformance.Case`, which has no proof modules, so a mutant that breaks a
proof still builds. A mutant is killed when any case gets a verdict other than
AGREE; three mutants move a case out of the model's scope instead of making it
disagree. The `mutants` Nix suite requires every mutant to be killed.

`conformance/authored_resolution.py` holds the coverage cases of ADR 0008 for the
first-scope resolution rules: each condition, a neighbor where it just does not
apply, and cases where two errors apply at once, each with requirement
identifiers. They are recorded as native version 5 records, with the error phase of
each statement, and the column-limit cases under a column limit of 5. All cases
agree with the model except four whose SQL it does not describe: a parenthesized
default, NOT NULL added to a table with rows, and a CREATE TABLE that runs with a
primary key or a default.
`python -m conformance.resolution_evidence --output DIRECTORY` freezes them as
corpus version 6. The judge claims such a corpus only in a separate,
owner-approved change.

`conformance/cases/` freezes the native cases in the current case format. Every model test
re-executes its original SQL and requires equality with that frozen record before
compiled and kernel checking. The files came from `just conformance --prove`;
regeneration requires the pinned native runner, never hand-editing a trace to
make a disagreement disappear.

## Additional bounded checks

- Transactions: admitted literal INSERT and UPDATE, commit, rollback, an open
  transaction at EOF, nested BEGIN, and a uniqueness failure. Errors preserve
  earlier visible writes and the original committed snapshot; later statements
  are not executed.
- Admission: unsupported SQL, a `statementReady` data-domain rejection, and
  `invalidDefinition` never count as agreement. Unsupported decoded cases also
  receive kernel proofs that `checkCase` is false.
- Storage and metadata: exact REAL bits, TEXT with invalid UTF-8/NUL, empty and
  nonempty BLOB, NULL, a populated 2000-column table, declaration aliases,
  timestamp defaults, primary/unique keys, and an explicit unique index.
- Failure detection: a wrong trace and falsely empty rows fail the compiled check
  and cannot acquire agreement proofs. An isolated production-model mutation
  that drops INSERT produces disagreement in compiled and kernel evaluation.
- Harness failures: a real exclusive SQLite lock prevents committed-state
  observation and returns `HARNESS_ERROR`; malformed JSON, versions and bytes
  also fail closed. A malformed input line does not poison the next valid line.

The model trace's final observation is proved equal to observing `runSql`, for
all scripts and initial databases. Finite case comparisons additionally use the
production `SupportedSql` checks. None of these statements proves universal
native refinement, arbitrary application-query preservation, or pilot acceptance.

## Native boundary and limits

For the original production-profile comparisons, the C-API runner loads the library beside the Nix-pinned SQLite executable,
checking version 3.51.0, exact source ID and MAX_COLUMN=2000. Each connection
keeps the build's compile-time limits unless a fixture lowers them, and the
recorder measures the limits that apply. Each connection
verifies library-default DQS_DML=1 and DQS_DDL=1 with `sqlite3_db_config`;
the pinned engine retains its default build configuration. Connections use native
autocommit, defensive mode off, trusted schema on, and writable schema off.
Explicit [native corpus profiles](execution-profile.md#native-corpus-profiles-adr-0005-in-progress)
can record additional settings and the native-only 3.53.4 pin. Such records
remain `MODEL_UNSUPPORTED`; they do not expand this model correspondence boundary.

Lean compares the catalog that resolution computes with `table_xinfo` (name,
declared type text, nullability, default and primary-key order) and with
`index_list` and `index_xinfo` (UNIQUE constraint keys and explicit index identity,
keys and uniqueness) after each statement. A difference is a disagreement. The
frontend refuses collations, descending keys of explicit indexes and partial
indexes, so their metadata in a native table is a harness error.

Per-statement observations retain primary and extended error codes; comparison
uses primary codes at the current model's granularity. TEXT/BLOB use bytes and
REAL uses its 64-bit pattern. Fixture cells use C-API parameter binding, including
positive and negative infinity. SQLite binds NaN as NULL: a requested NaN REAL
therefore produces an initial-state disagreement, not an invalid-SQL harness error. A second connection observes committed state while
a transaction is open. Contention that prevents observation is a harness failure,
not semantic evidence. Native statements have a five-second progress deadline
and a 100 ms lock wait; outer test/recipe deadlines also bound complete runs.
Native tables are read from `sqlite_schema` and their PRAGMAs on each observation,
for the visible and the committed view; no schema is parsed to observe them.
Benchmark cases are sent
through one JSON-lines runner process; reports separate native acquisition and
compiled batch time (including transport). Optional proof-term emission and kernel
checks run separately, outside the timing.
Parsing is bounded to five seconds, each compiled batch to 30 seconds, and
concrete kernel checks to 120 seconds. The 2,000-column case is compiled only.

The tier-two denominator is the 16 authored derived cases, plus the
injected transport regression. [Stateful generation](conformance-generation.md)
and [frozen corpus progress](conformance-progress.md) have separate denominators.
W3–W7 were approved and implemented after the prototype review. Original static
`alter3` fixtures retain their unsupported view dependency; the runtime pilot
records unsupported objects without removing them to inflate agreement.
