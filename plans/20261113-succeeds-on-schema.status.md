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
