# Remove the migration verifier product (ADR 0021)

Created 2026-10-21. Status: DONE (2026-10-21).
Status file: [status](20261021-remove-verifier-product.status.md).
Specification: [ADR 0021](../docs/adr-0021-remove-the-verifier-product.md), D1 to D5.
Depends on: [S1](20261021-surface-s1.task.md) (the surface package and its layer test).

## Scope

The repository keeps the model, its conformance evidence, the parser and the surface, and loses
the migration verifier: its CLI, its library, its kernel gate, its installed runtime, its release
and their tests and documents (ADR 0021, D1). Nothing that stays may need a removed part (D2).

Out of scope: the SQL text task, which comes after this one; renaming the repository; deleting
published releases.

## Outcome

1. **The product is gone.** The paths of ADR 0021 D1 are deleted, with every caller, Nix
   attribute, suite, justfile recipe, CI step and document link changed. No file that stays names a
   removed module, package, program or document, except the history of ADR 0021 D4 (ADRs, plans,
   review records, reports).
2. **The conformance runtime has no product code.** It is the pinned Lean toolchain, the model
   package, the conformance runner's outputs and the parser library. `subject.conformance` in
   `integrity/judge.nix` builds no verifier library, exporter or gate program.
3. **The restriction examples use the runner.** `conformance/restriction_examples.py` shows each
   restriction id reached from SQL through `conformance-runner`, with the same table of examples
   and the same restriction ids.
4. **The kept tools start from the model.** The `lean_libraries` fixture, the API reference and the
   documentation inventory use the model's roots, not `SqliteVerifier`. `just build` and the `lean`
   and `lib` links point at the conformance runtime or its parts.
5. **The model loses only the gate's codecs.** `Codec/Source.lean`, `Codec/SourceExamples.lean` and
   the script record are deleted; every law stays.
6. **CI.** The check job builds and tests the kept parts only; the `release` job, the archive steps,
   the bundle phase and `adr3-p1.yml` are gone. The `mutants` and `verdict` jobs run as before.
7. **Documents.** `README.md` describes the model, the evidence and the surface. The product's
   documents (ADR 0021, D1) are deleted. The ADRs that only the product used say "Superseded by
   ADR 0021" in their header. ADR 0008 "Where resolution runs", ADR 0011 decision 6, ADR 0016 D2
   and ADR 0017 D6 are amended where they name the product. `.github/CODEOWNERS` keeps only the
   development integrity lines.

## Tests

- **The predictions do not change.** The predictions of every frozen corpus are byte-identical to
  the predictions before the task, and `just verdict` passes.
- **The restriction examples.** `tests/conformance_restriction_examples_test.py` passes through the
  runner, and gives the same restriction id for each example as before.
- **No dangling names.** A search of the kept files finds no import, path or link of a removed
  part (outcome 1); the status file records the search and its result.
- **The kept suites.** `just test-full`, `just test-nix` and `just test-scheduled` pass; the
  surface suite passes, with its layer test changed to the runtimes that remain.
- The status file records the time of `just test-full` and the size of the conformance runtime's
  closure before and after the task.

## Key points

- **The runtime fixture.** Several model tests (`column_default_*`, `column_extension_test`,
  `failed_catalog_observation_test`, `shared_table_shape_test`, `conformance_trace_test`) import
  only model or runner modules, but `lean_libraries` in `tests/runtime_fixtures.py` requires
  `SqliteVerifier.olean`. They stay, with the fixture changed.
- **The runner and restrictions.** `conformance-runner --predict` already reports a model
  restriction with its id (`Predict.lean`, `restricted` and `restriction`). An example whose SQL
  the frontend refuses keeps the `frontend` result.
- **Coverage.** `conformance/coverage_catalog.py` names six `SqliteVerifier` theorems for the axiom
  audit (`coverage_evidence.py`). The audit of product theorems goes; if the audit has no theorem
  left, it goes too.
- **Tests that guard a removed boundary.** `test_model_ownership.py` and `test_model_package.py`
  use copies of `packages/sqlite-verifier` as fixtures; `conformance_frontend_boundary_test.py` and
  `test_frontend_namespace.py` check that the harness does not import `migration_check`. Keep the
  checks that still guard a kept boundary (for example the model's imports), and delete the rest.
- **Shared Nix and CI code.** `build-support/default.nix`, `tests.nix`, `sources.nix`,
  `api-reference.nix`, `public-documentation.nix`, `tools/ci_checks.py`, `tools/ci_store_gc.py`,
  `tools/test_reports.py` and `tests/ci_scope.py` name product parts beside kept ones.
- **The judge.** The lock covers `judge/`, the claims, the corpora and the oracle
  (`integrity/judge.nix`). This task changes the subject's build, not the lock: the lock check
  (`nix-build integrity/judge.nix -A locked`) passes with the lock file unchanged.
- **Protected files.** The task changes `.github/workflows/` and `.github/CODEOWNERS`, so its pull
  request needs the owner's review (ADR 0011, decision 4).
- **Historical reports.** The frozen suite reads `reports/20261001-adr5-c5-authored*` and
  `reports/20261006-grouped-immediate-transactions`; the reports stay.
