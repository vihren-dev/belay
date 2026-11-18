# Status of derived-column automation

Created 2026-11-17. DONE. [Task](20261117-derived-column-automation.task.md).

The three laws already have examples in tests/surface/Schema/Tests/DerivedColumnOnSchema.lean.
The proof attempt in Tooling/Counterexamples/CheckAutoProof.lean and the route
selection of sql_auto are the user entry points. Both entry points now try the derived-column laws on a schema-scoped claim.
CheckSchemaNote.lean exercises the two reads, the success claim and the
unscoped fallback. tests/surface_check_schema_note_test.py checks the
printed scripts.

The guide now shows the proof for the named-column read. The regression
also checks the schema-scoped SELECT * counterexample against SQLite.

The guide distinguishes a direct law application from both automatic searches.

The Linux and macOS checks passed in [CI run 44194426109](https://github.com/vihren-dev/belay/actions/runs/44194426109).
The full Linux suite includes the three suggested proofs and the native SQLite
replay. The locked verdict matches main. All 98 Nix infrastructure tests and
the scheduled Nix checks passed.
