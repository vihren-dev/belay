# Status: `DROP INDEX` and `DROP TABLE` (ADR 0014, slice 7)

Created 2026-10-20. Status: DONE (pull requests #191 and #192).
Task file: [task](20261020-drop-index-table.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D7.

## Progress

- 2026-10-20: native behaviour checked with 3.51.0: `no such table` and `no such index`
  (also for an object of the other kind), `IF EXISTS`, `table sqlite_master may not be
  dropped` (also for `sqlite_schema` and with `IF EXISTS`), `index associated with UNIQUE or
  PRIMARY KEY constraint cannot be dropped`, names compared with ASCII case ignored,
  `sqlite_stat1` can be dropped, and ROLLBACK restores a dropped table. `foreign_keys` is
  off by default.

- 2026-10-20: the model, the frontend and the tests (commit "DROP INDEX and DROP TABLE").
  - Frontend `belay/sqlite/syntax_drops.py`; Lean `Syntax.Statement.dropTable` and
    `dropIndex`, `Resolved.Statement.drop positions` (kind `drop`),
    `Resolution/CatalogDrop.lean` (`Catalog.drop`, `keptBelow`, `Catalog.tableObjects`, the
    names lemma), `Resolution/Drops.lean` (`resolveDropTable`, `resolveDropIndex`), the
    prepare errors `noSuchIndex` and `tableMayNotBeDropped`, the restriction
    `drop-constraint-index`, and `Database.drop` in execution.
  - Laws: `CatalogStep.remove`, the DROP cases of the names, catalog-agreement and
    resolve-state laws; `step_extends` excludes DROP (nothing else uses it).
  - `Resolution/DropExamples.lean`; `conformance/authored_drops.py` (21 cases, all agree
    with kernel proofs), `drop_evidence.py` (corpus 35), `drop_mutants.py` (three mutants,
    all killed). The requirement case `drop-index` now agrees.

- 2026-10-20: review of "DROP INDEX and DROP TABLE": four must findings (a policy literal,
  missing proof sketches, a file over 200 lines). Fixed in "refactor: DROP review":
  `constraintIndexName`, sketches, and `Resolution/DropSpec.lean` with the DROP resolution
  laws.

- 2026-10-20: the first suite run failed: the Nix suites copy only the frontend modules
  that `tests/conformance_frontend.json` lists. Fixed in "fix: declare the DROP frontend
  module for the Nix suites" (review clean). Then `just test-full`, `just test-nix` and `just
  test-scheduled` pass. CI time with forced rebuilds: harness 22 s, model 414 s, frozen
  142 s, mutants 648 s. Verdict: 33 upstream cases newly agree (v3 +2, v4 +10, v5 +21), none
  leave AGREE, and corpus 35 has 21 AGREE. Pull requests #191 (A) and #192 (B). This is the
  last slice of ADR 0014.

## Remaining

- None. DONE.
