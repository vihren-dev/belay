# Status: the theorems of the other Valid atoms (ADR 0022, slice 3)

Created 2026-10-23. Status: open; the task file waits for the owner decisions below. No proof
work has started.
Task: [task file](20261023-valid-atoms-theorems.task.md).
Specification: [ADR 0022](../docs/adr-0022-database-validity.md), D1, D3 and D4 (slice 3).
Needed by: [ADR 0017](../docs/adr-0017-user-surface.md), S4.
Depends on: [slice 2](20261023-keys-unique.task.md); part 1 is in this line of changes, part 2
is in progress in another workspace.

## Relevant files

- The atoms: `packages/belay-sqlite-model/Belay/Sqlite/Model/DatabaseConstraints.lean`
  (`Table.NotNull`, `Table.ChecksHold`, `Table.TypesFit` and their database forms),
  `DatabaseConstraintChecks.lean` (`Table.constraints_iff` and the three `_iff` lemmas),
  `LiteralData.lean` (`checkHolds`, `checksHold`, `typesFit`, `notNullRows`, `constraints`).
- The statement step: `StatementStep.lean`, `StatementRun.lean` (`checkedWrite`),
  `Execution.lean` (`step`: ADD COLUMN, CREATE, DROP), `Upsert.lean`, `UpsertRun.lean`,
  `SqlState.lean`.
- The row engine: `ForeignKeyWrites.lean`, `RowEngine.lean`, `ForeignKeyRows.lean`,
  `RowInsert.lean`, `TriggerRun.lean`, `ForeignKeyPhases.lean`.
- ADD COLUMN: `Database.lean` (`Database.addColumn`), `Resolution/ReadDefaults.lean`
  (`readDefaultValue`), `Resolution/ReadDefaultLaws.lean` (`readDefaultValue_stored`),
  `Resolution/AddColumn.lean` (`strictDefaultFits`), `Resolution/ExprAny.lean`
  (`Resolved.Expr.readsBelow`), `Resolution/StrictTypes.lean` (`StrictType.fits`).
- The runs: `StatementStep.lean` (`runSqlFrom`, `runSql`), `ScriptRun.lean` (`runScriptFrom`).
- Slice 2 to reuse: `KeysUniqueFrame`, `KeysUniqueWrites`, `KeysUniqueUpsert`,
  `KeysUniqueCreate`, `KeysUniqueAddColumn`, `KeysUniqueDrop`, `DropPositionLaws`,
  `ExprAppendLaws`, `KeysUniqueExamples`; from part 2 (other workspace): `KeysUniqueKeyState`,
  `KeysUniqueKeySteps`, `KeysUniqueTriggers`, `KeysUniqueRowDelete`, `KeysUniqueRowUpdate`,
  `KeysUniqueRowInsert`, `KeysUniqueRowEngine`, `KeysUniqueStatement`.
- Tests: `tests/shared_table_shape_test.py` (`compile_checks`), `tests/test_model_package.py`.

## Size estimate

Measured on 2026-10-23. Slice 2 part 1 is 1279 Lean lines in 10 modules (with its examples);
part 2, at its commit `pvmyqwkoowor` (before its run theorems), is 824 lines in 8 modules.
Slice 3 has three atoms, but they read one row at a time, so one argument can serve the three
(task file, "Key points").

| Work | Lines |
| --- | --- |
| Frame lemmas and the laws of `setRows`, append, DROP and a sublist for the three atoms | 120–170 |
| Plain INSERT, UPDATE and DELETE, upsert, the forms that keep the database | 150–220 |
| CREATE TABLE, CREATE INDEX, CREATE TRIGGER and DROP (no condition) | 80–120 |
| ADD COLUMN with the three conditions | 150–220 |
| Examples of part 1 (the five counterexamples) | 60–90 |
| **Part 1** | **560–820** |
| Row engine with decision 1 a) (part 2's proofs with a parameter, and three instances) | 260–450 |
| The statement theorems over all of `runStatement` | 80–120 |
| Run theorems for `runSqlFrom` and `runScriptFrom`, and the corollary of the four atoms | 100–180 |
| Examples of part 2 (SET NULL, the concrete run) | 30–60 |
| **Part 2** | **470–810** |

Total: about 1000–1600 lines in 8 to 13 new modules. With decision 1 b), the row engine is a copy
of part 2's proofs for a new invariant: about 600–800 lines instead of 260–450. The pragma forms
of ADR 0019 slice 2 add about 20–60 lines when they land.

The size is near that of slice 2, so the task file proposes the same split into two parts
(decision 2).

## Owner decisions

1. **The invariant of the row engine.** Slice 2 part 2 proves the row engine with an invariant
   that is fixed to `Database.KeysUnique` (`KeyState.KeysUnique`, `NestedRun.KeepsKeys`). Its
   proofs rest mainly on two facts of the atom: a table that passes `LiteralData.constraints`
   satisfies it, and a table with a sublist of the rows and the same entry satisfies it. The
   three atoms of this slice have the same two facts.
   - a) Slice 3 makes the atom a parameter of part 2's proofs, in `refactor:` commits after
     part 2 lands, and gets the four atoms as instances.
   - b) Slice 3 copies the structure of part 2's proofs for one invariant of the three atoms,
     and part 2 stays as it is.
   - c) Part 2 makes the atom a parameter before it lands.

   Recommendation: a). It removes about 300 lines of copy (a measured cost, R18), and part 2
   lands without a change. Option c) changes work that is in progress in another workspace.
2. **The split.**
   - a) One task file in two parts (task file, "Parts"), each with `just test-full` and
     `just verdict`, as slice 2 (its decision 2 a)).
   - b) One part.

   Recommendation: a). Part 1 can start now, on slice 2 part 1; part 2 needs slice 2 part 2.

The conditions of ADD COLUMN in the run theorems follow slice 2's decision 1, option A: a
hypothesis on each reached ADD COLUMN, and slice 4 proves the resolver facts. This adds two
resolver facts to slice 4: each CHECK of a resolved table reads only its columns, and each
resolved ADD COLUMN has `strictDefaultFits`.

## Findings

A proof that fails is recorded here with a counterexample (ADR 0022, D3). None yet.

## Progress log

- 2026-10-23: the task file and this status file. Checked natively with SQLite 3.51.0: SET NULL
  on a NOT NULL child column fails with `NOT NULL constraint failed: c.x` and keeps the parent
  row (log: `build/agent-logs/adr22s3-setnull-probe.log`).
