# Status: the theorem of "keys unique" (ADR 0022, slice 2)

Created 2026-10-23. Status: open; no code yet. Three owner decisions are open (below).
Task: [task file](20261023-keys-unique.task.md).
Specification: [ADR 0022](../docs/adr-0022-database-validity.md), D3 and D4 (slice 2).
Needed by: [ADR 0017](../docs/adr-0017-user-surface.md), S4.

## Relevant files

- The atom: `packages/belay-sqlite-model/Belay/Sqlite/Model/DatabaseConstraints.lean`
  (`Table.KeysUnique`, `Database.KeysUnique`), `DatabaseConstraintChecks.lean`
  (`uniqueRows_iff`, `Table.keysUnique_iff`), `LiteralData.lean` (`keyEqual`, `uniqueRows`,
  `constraints`), `Resolution/Catalog.lean` (`Catalog.uniqueKeys`).
- The statement step: `StatementStep.lean` (`runStatement`, `runSqlFrom`, `runSql`),
  `StatementRun.lean` (`checkedWrite`), `Execution.lean` (`step`), `Upsert.lean`,
  `UpsertRun.lean`, `SqlState.lean`.
- The row engine: `ForeignKeyWrites.lean`, `RowEngine.lean`, `ForeignKeyRows.lean`,
  `RowInsert.lean`, `TriggerRun.lean`, `ForeignKeyPhases.lean`.
- Schema changes: `Database.lean` (`Database.drop`, `Database.addColumn`),
  `Resolution/CatalogDrop.lean`, `Resolution/Keys.lean`, `Resolution/ExprAny.lean`,
  `ExprEval.lean`.
- The runs: `ScriptRun.lean` (`runScriptFrom`); the surface run in
  `packages/belay/Belay/Sqlite/ProgramRun.lean` (`Run.checked`), which this slice does not change.
- Laws to reuse: `DatabaseLaws.lean`, `StepCatalogLaws.lean`, `SqlStateLaws.lean`,
  `QueryPlainLaws.lean` (the pattern of a mutual induction over `Expr`), `Comparison.lean`.
- Tests: `tests/shared_table_shape_test.py` (`compile_checks`), `tests/test_model_package.py`.

## Size estimate

Measured from the definitions on 2026-10-23, in Lean lines with docstrings:

| Work | Lines |
| --- | --- |
| Frame lemma and the frame facts of `setRows`, `addColumn`, append and drop | 120–160 |
| Lookup lemma (symmetry and transitivity of `keyEqual`) | 60–90 |
| Plain INSERT, UPDATE and DELETE | 60–90 |
| Upsert (an invariant over the steps of `upsertSteps`) | 100–140 |
| CREATE TABLE, CREATE INDEX, CREATE TRIGGER | 100–140 |
| ADD COLUMN (with the lemma that an expression that reads below a width ignores appended cells) | 150–220 |
| DROP (with the renumbering of `afterDrop`) | 120–180 |
| Examples of part 1 | 40–60 |
| **Part 1** | **750–1080** |
| Row engine (an invariant over `KeyState`, by induction on fuel, through CASCADE, SET NULL, SET DEFAULT, triggers, `RAISE` and REPLACE) | 300–420 |
| The statement theorem over all of `runStatement` | 60–90 |
| Run theorems for `runSqlFrom` and `runScriptFrom` | 120–180 |
| **Part 2** | **480–690** |

Total: about 1200–1800 lines in 9 to 13 new modules. The row engine is the largest single form
and the largest risk. The pragma forms of ADR 0019 slice 2 add an estimated 40–120 lines when
they land, mostly in the row engine for `recursive_triggers`.

## Owner decisions

1. **How the run theorems state the conditions of ADD COLUMN and DROP** (task file,
   "Conditions"). A run can reach an ADD COLUMN or a DROP that needs a fact which this slice does
   not prove for the runs.
   - a) A hypothesis: each ADD COLUMN and DROP that the run reaches meets its condition, on the
     database at that point. Slice 4 then removes the hypothesis with its theorems.
   - b) The run theorems cover only scripts without ADD COLUMN and DROP.
   - c) No run theorem in this slice; slice 4 adds them.
   - d) This slice also proves that the runs keep `Table.RowsWide` and `Catalog.Valid`, and the
     resolver closure of DROP (work of slice 4, about 300 more lines).

   Recommendation: a). The theorem is true as stated, S4 can use it at once for the guide's
   programs, and slice 4 removes the hypothesis without a change to the statement theorem.
2. **The split.**
   - a) One task file in two parts (task file, "Parts"), each with `just test-full` and
     `just verdict`.
   - b) Two task files, one for each part.
   - c) One part.
   - d) Part 1 only; the row engine goes to a later slice, and the statement theorem covers the
     writes through the row engine only when no rules apply.

   Recommendation: a). Part 1 is useful alone (the lookup lemma and most forms), part 2 has one
   subject (the row engine), and one task file keeps the conditions and the tests in one place.
   Option d) leaves out the writes with foreign keys on, which the guide's programs use.
3. **The surface run.** ADR 0022, D3 names `runSql`. The surface runs `runScriptFrom`: `db.run`
   is `Run.checked` of it (`packages/belay/Belay/Sqlite/ProgramLaws.lean`).
   - a) Prove the run theorem for both.
   - b) Prove it for `runSqlFrom` only; S4 proves the step to `runScriptFrom`.

   Recommendation: a). S4 needs the theorem for the run of the surface, and `runScriptFrom`
   uses the same statement step (`runScriptStep`), so the added work is small (about 60 lines,
   in the estimate above).

## Findings

None yet. A proof that fails is recorded here with a counterexample (ADR 0022, D3).

## Progress log

- 2026-10-23: the task file and this status file.
