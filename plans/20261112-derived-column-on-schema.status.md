# Status: short proofs of the derived-column migration on a schema

Created 2026-11-12. Task: `20261112-derived-column-on-schema.task.md`. Issue #376.
Status: in progress; reads (a), success (b), example (c) and the test of the page with a fresh agent done; the end checks are pending.

## References

- Laws: `packages/belay/Belay/Sqlite/Programs/StatementRunLaws/DerivedColumnMigration.lean`,
  `DerivedColumnQueries.lean`, `DerivedColumnReads.lean`.
- Site and reads: `packages/belay/Belay/Sqlite/Schema/Columns/DerivedColumnMigration.lean`,
  `DerivedColumnReads.lean`.
- Model steps: `addColumn_plain_step`, `backfill_step`, `derivedColumn_state` in
  `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/`.
- Computed check (a): `Schema/Columns/DerivedColumnSiteCheck.lean`, `DerivedColumnReadCheck.lean`,
  `Programs/StatementRunLaws/DerivedColumnSchema.lean` (all under `packages/belay/Belay/Sqlite/`); model
  parts `Queries/Evaluation/ExprFormChecks.lean` and `Schema/Dispatch/SelectTableParts.lean` (under
  `packages/belay-sqlite-model/Belay/Sqlite/Model/`).
- Success (b): `succeedsCheck` and `succeeds_of_check` in
  `packages/belay/Belay/Sqlite/Programs/StatementRunLaws/DerivedColumnSuccessCheck.lean`; model laws
  `derivedColumn_script_ok` (`Programs/StatementRunLaws/DerivedColumnSuccess.lean`),
  `runScriptStep_ordinary_ok` (`Programs/Scripts/OrdinaryStepOk.lean`), `runStatement_backfill_ok`
  (`Schema/Writes/DerivedColumnUpdateRun.lean`) and `Table.appendCells_checked`
  (`Schema/Writes/DerivedColumnConstraints.lean`).
- Example (c): `tests/surface/Schema/Tests/DerivedColumnOnSchema.lean` with `db/schema.sql` and
  `db/migrations/0003_email_lower.sql` beside it. It replaces the hand proof
  `DerivedColumnSchemaPremise.lean`, which is deleted.
- Page for agents: `docs/guide/agents.md`.

## Progress

- 2026-11-12: task and status files.
- 2026-11-12: reads (a). `siteCheck` and `Site.ofCheck` give the site from the catalog; `readCheck` and
  `Site.ReadPreserved.ofCheck` give the read facts; `preservesCheck`, `preserves_of_check` and
  `preserves_of_check_forall` give `M preserves Q on schema` from the scripts as `sql` text. Fixture
  `DerivedColumnCheckBoundaries` covers the false cases and a second schema. The check works on a `db!`
  schema and on a run of a script.
- 2026-11-12: success (b). `succeedsCheck` adds to the site facts the resolution of both statements, no
  STRICT type of the new column, unchanged keys, checks and keys of old columns, and an assigned value
  without a fallible call, clock or counter. `succeeds_of_check` gives `Succeeds M (·.HasCatalog schema)`.
  Fixture `DerivedColumnSuccessBoundaries`: success on `shop` and on a second schema; false checks for a
  STRICT INTEGER column and a fallible value; `#sql_check` gives `false` for the STRICT case.
- 2026-11-12: example (c). `DerivedColumnOnSchema` proves the two reads and the success claim in one line
  each, from the SQL files. Its test builds it in a consumer Lake project that requires only `belay`.
  `docs/guide/agents.md`, `skills/belay/SKILL.md` and the template `MigrationClaims.lean` name the laws.
  The boundary fixture also checks a `db!` schema.
- 2026-11-12: test of the page with a fresh agent. From `docs/guide/agents.md` and the skill only, an agent
  proved in a new project the two reads and the success claim with the three laws; `lake build` and
  `belay-sql-check` passed, with logical axioms only. From its report, the skill now says to paste the
  `Construction:` statements in `r#"…"#` (they can contain `"`), puts the library law first in the steps
  for `unknown`, and names the count of SQL sources in place of the count of modules.
- 2026-11-12: the first `just test-full` failed in `test-source`: the model root did not import the new
  model modules, the skill templates had no Lean file category (from the page for agents, #373), and the
  test of #371 was in no Nix suite, so it ran on the host with the wrong runtime. Fix commits are after the
  commits of each issue.
- 2026-11-12: the second `just test-full` failed in `surfaceSelect`: `test_background_checking` gave
  unknown for a claim that it proves. Bisection found the #371 commit: the check of a command had only nine
  tenths of the budget, so that the reason of an unknown result stays. A fix commit after the #371 commits
  gives the check the whole budget again and keeps the unknown outcome, with its reason, when the end of
  the budget aborts the command.

## Tests of each commit

- Reads (a): `tests/surface_derived_column_test.py -k boundaries`.
- Success (b): `tests/surface_derived_column_test.py -k "success_of_the or boundaries"`.
- Example (c): `tests/surface_derived_column_test.py` (the consumer test needs the runtime of
  `just build`).
