# Status: remove the migration verifier product

Created 2026-10-21. Status: OPEN.
Task: [task file](20261021-remove-verifier-product.task.md).
Specification: [ADR 0021](../docs/adr-0021-remove-the-verifier-product.md).

## Relevant files

- Removed: `migration_check/`, `bin/`, `packaging/`, `examples/`, `packages/sqlite-verifier`,
  `packages/verifier-gate`, `build-support/runtime.nix`, `lean4export.nix`, `case-seeds.nix`,
  `case_seed.py`, `library_lakefile.py`, `.github/workflows/adr3-p1.yml`.
- Changed: `build-support/default.nix`, `tests.nix`, `sources.nix`, `api-reference.nix`,
  `public-documentation.nix`; `conformance/restriction_examples.py`, `coverage_catalog.py`,
  `coverage_evidence.py`; `tests/runtime_fixtures.py`, `tests/nix_suites.json`, `tests/ci_scope.py`;
  `tools/api_reference.py`, `public_doc_inventory.py`, `ci_checks.py`, `ci_store_gc.py`,
  `test_reports.py`; `.github/workflows/ci.yml`, `.github/CODEOWNERS`; `justfile`; `README.md`.
- The model's gate codecs: `packages/belay-sqlite-model/Belay/Sqlite/Model/Codec/Source.lean`,
  `SourceExamples.lean`, the script record in `Codec/Resolution.lean`.

## Progress log

- 2026-10-21: ADR 0021 and the task file, from a survey of the dependencies on the product. The
  SQL text task now depends on this task and serves the harness only.
- 2026-10-21: review of ADR 0021 and the task: one finding, in the SQL text task (the harness
  also reads each statement's end, in `native_trace.py`); fixed. The second review had no findings.
