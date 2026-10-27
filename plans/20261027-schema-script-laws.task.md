# Schema-script laws: step, frame and success laws for the table rebuild

Created 2026-10-27. Status: OPEN.
Status: [progress](20261027-schema-script-laws.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S6;
[S6 automation](20261024-s6-automation.task.md), part 3 outcome "the rebuild
example", and the gap analysis "Part 3 outcome (a), the rebuild example:
stopped at a gap (2026-10-27)" in its [status file](20261024-s6-automation.status.md);
[table rebuild](20261024-table-rebuild.task.md) (done).

## Purpose and boundary

The guide's table rebuild is a script of nine statements: a pragma, BEGIN,
CREATE TABLE, INSERT SELECT, DROP TABLE, a rename, `PRAGMA foreign_key_check`
and COMMIT. The table-rebuild task models each statement and proves what one
successful or failed step can do. S6 part 3 needs three claims about the whole
script. The model and the surface cannot prove them yet:

1. The script keeps the rows of a table that it does not change (the guide's
   `sessions`), for every database of a site.
2. The script succeeds when the source rows meet the constraints of the new
   table (the guide's "no NULL names").
3. The wrong rebuild (the drop with foreign-key enforcement on) does not keep
   them. This is a refutation.

The owner decided on 2026-10-27 (option A) that a separate task adds the
missing laws as general laws, and that the rebuild fixture then proves the
three claims. The laws hold for any tables, names and scripts under explicit
premises (owner rule of 2026-10-27: each statement as general as the proof
allows). The guide's tables appear only in `tests/surface`.

This task changes no SQL meaning, no execution, no prediction, no corpus, no
claim and no judge file. With its fixture, S6 automation part 3 is complete.

## Required outcomes

- **Step laws for the schema and transaction statements.** At the level of
  `runScriptStep`, each of CREATE TABLE, DROP TABLE, the modeled pragmas
  (at least `foreign_keys` and `foreign_key_check`), BEGIN and COMMIT has:
  - a failure law: a failed step keeps the database;
  - a success law: the database after success, given as a function of the
    database before it (catalog and rows);
  - a frame law: a table that the statement does not name keeps its rows,
    with the table found by name in the database after the step, under an
    explicit premise that excludes indirect effects on it. DROP TABLE runs an
    implicit DELETE, so with foreign-key enforcement on it can change a child
    table through a cascade (`RebuildRuns.unsafe_rebuild_cascades`); the
    premise is, for example, enforcement off, or no foreign key of the
    observed table that names the dropped table.
  Where a law exists at another level (`runStatement`, `step_rewrite_ok`,
  `runScriptStep_failed_frame`, `StatementKeeps.ofOwnRun`, the drop position
  laws), the new law builds on it instead of repeating it.
- **Frames and read certificates by table name.** A read certificate and its
  obligations (`ReadCertificate.Obligations`,
  `runScriptStep_simpleTable_output_append`) state their facts for the table
  found by name in each database, so they stay usable when an earlier table
  is dropped and the position of the observed table changes. The current
  single-position form is replaced, and all its callers move (repository rule
  "Replaced code"). Where a caller needs the position, the position comes from
  the name lookup.
- **Translation over several end states.** `Migration.translatesAt_of_observations`
  takes one reached connection and one output count. A general form takes, for
  each possible execution of the migration, its own reached connection. The
  current form follows as an instance, or it is replaced and its callers move.
  The derived-column task (`plans/20261027-derived-column-laws.task.md`) may
  have changed the callers.
- **A success law for INSERT SELECT.** For any target table and any source
  query whose productions are certain and fault-free, no execution fails and
  the result is the upsert of the produced rows, when the produced rows meet
  the target's constraints. The constraints are: values that fit the column
  types after affinity conversion (`typesFit`, which a STRICT table checks),
  NOT NULL, distinct and absent unique keys, valid rowids, CHECK constraints,
  no trigger, and no foreign-key failure under the connection's enforcement
  state. It needs a law that the
  productions of a plain scan are the rows of the table, without a fault
  (`Query.productions`), and an induction over the rows for the upsert
  (`upsertRow_ok`, `upsertSummary_keysUnique`).
- **The tactics know the new statements.** `sql_run` and `sql_commute` choose
  the new step and frame rules for these statements. Unproved premises stay as
  goals, as for the existing rules.
- **The rebuild fixture.** In `tests/surface`, next to `RebuildRuns.lean`, the
  three claims are proved from the general laws:
  - the preservation claim for every database of a site whose catalog is the
    guide's schema (a premise: with a view or trigger named in the script, or
    another `customers`, the claim is not provable);
  - the success claim when no source name is NULL;
  - the refutation of the wrong rebuild by `sql_refute`, with
    `PRAGMA foreign_keys = ON` first (a new connection has enforcement off,
    in the model and in native SQLite).
  The status file records the guide changes that the S6 status file lists,
  and any that this task finds.

## Tests and acceptance

- Kernel examples for each new step, frame and success law on concrete
  databases, including a failing case for each premise of the INSERT SELECT
  success law (a NULL into NOT NULL, a duplicate key, a CHECK failure, a
  value that does not fit a STRICT column type), and a DROP TABLE with
  enforcement on whose cascade changes the observed table.
- A frame example where DROP TABLE of an earlier table moves the observed
  table, and the certificate still applies.
- Native SQLite checks the concrete results that those examples state, and
  the three fixture claims on concrete databases, with the native helpers of
  the surface tests.
- Axiom audits of the fixture theorems allow only `propext`,
  `Classical.choice` and `Quot.sound`.
- All prediction files stay byte-identical to the base (`nix-build
  integrity/judge.nix -A predictions`).

Two acceptance parts: (1) the general laws (step, frame, certificate,
translation and success laws); (2) the tactic rules and the rebuild fixture.
Each coherent commit gets focused checks, dev-build and independent review.
Each part ends with `just dev-build`, then `just test-full` and `just verdict`.
At task end, run `just test-nix` and `just test-scheduled-checks` once. They
also count as the task-end checks of the S6 automation task. Only Nix results
are acceptance evidence.

## Existing interfaces and tricky points

- The S6 status gap analysis lists the pieces with size estimates: about 60
  lines for the translation, about 10 files for the certificate positions,
  about 250 lines for the frames, 250 to 350 lines for the success law, and
  about 100 lines for the tactic rules.
- `runStatement_insertSelect_none_effects` (`InsertSelectLaws.lean`) gives an
  error that keeps the database, or the effect of an upsert of known rows.
  The success law is the other direction.
- The rename guard is `Catalog.sameOutline`. After the guide's rebuild, the
  foreign-key atoms come from the database (what `PRAGMA foreign_key_check`
  reports), not from a frame law. The claims of the fixture do not need them.
- `PRAGMA foreign_key_check` returns the violations and does not abort the
  script. The fixture states what the script returns.
- The derived-column task replaces the `NormalizedField*` modules, and one of
  them calls `translatesAt_of_observations`. The implementation of this task
  starts on a base that contains the derived-column task.
- The surface suite takes about 1020 s of its 1200 s limit. Put new kernel
  examples in a suite with headroom (`surfaceChecks`), or keep them small. If
  the surface suite would pass its limit, stop and report with options.
- Files stay below 200 lines, with checked public docstrings, plain-words
  statements and proof sketches.
