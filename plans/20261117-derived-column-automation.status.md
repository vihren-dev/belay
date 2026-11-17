# Status of derived-column automation

Created 2026-11-17. Open. [Task](20261117-derived-column-automation.task.md).

The three laws already have examples in tests/surface/Schema/Tests/DerivedColumnOnSchema.lean.
The proof attempt in Tooling/Counterexamples/CheckAutoProof.lean and the route
selection of sql_auto are the user entry points. Both entry points now try the derived-column laws on a schema-scoped claim.
CheckSchemaNote.lean exercises the two reads, the success claim and the
unscoped fallback. tests/surface_check_schema_note_test.py checks the
printed scripts. The Nix checks are pending.
