# Status: `succeeds … on schema`, and the public rebuild example as a fixture

Created 2026-11-13. Task: `20261113-succeeds-on-schema.task.md`. Issues #382 and #384.
Status: IN PROGRESS.

## References

- `preserves … on` (#375): `packages/belay/Belay/Sqlite/Programs/Reasoning/MigrationPatternSyntax.lean`.
- `succeeds`: `packages/belay/Belay/Sqlite/Programs/Claims/SuccessSyntax.lean`.
- Schema from a premise: `domainSchemas` in
  `packages/belay/Belay/Sqlite/Tooling/Counterexamples/CheckDomain.lean`; it already enters `Succeeds`.
- Rebuild fixtures: `tests/surface/Schema/Tests/RebuildGuide.lean`, `RebuildCheck.lean`,
  `RebuildKeeps.lean`, `RebuildSucceeds.lean`; test `tests/surface_rebuild_test.py`.

## Progress

- 2026-11-13: task and status files.
- 2026-11-13: owner decision: the README uses `badMigration` and `fixedMigration` too. Task file
  review: 2 findings fixed (b1b86a51).
- 2026-11-13: #382: one `succeeds` syntax with an optional `on` and `where`
  (`SuccessSyntax.lean`); expansion and guard-position examples in `SuccessSyntaxExamples.lean`;
  `packages/belay/README.md`, the page for agents, the skill, its template and
  `DerivedColumnOnSchema.lean` use `M succeeds on shop`. Tests: `tests/surface_success_test.py`,
  `tests/surface_derived_column_test.py` (host, without the consumer-project test, which needs
  Nix), `tests/surface_migration_patterns_test.py`.
