# Status: remove the migration verifier product

Created 2026-10-21. Status: OPEN.
Task: [task file](20261021-remove-verifier-product.task.md).
Specification: [ADR 0021](../docs/adr-0021-remove-the-verifier-product.md).

## Relevant files

- Removed: `migration_check/`, `bin/`, `packaging/`, `examples/`, `packages/sqlite-verifier`,
  `packages/verifier-gate`, `build-support/runtime.nix`, `lean4export.nix`, `case-seeds.nix`,
  `case_seed.py`, `library_lakefile.py`, `.github/workflows/adr3-p1.yml`,
  `conformance/coverage_evidence.py`, the product documents and experiments.
- Changed: `build-support/default.nix`, `tests.nix`, `sources.nix`, `api-reference.nix`,
  `public-documentation.nix`; `conformance/restriction_examples.py`, `coverage_catalog.py`;
  `tests/runtime_fixtures.py`, `tests/nix_suites.json`, `tests/ci_scope.py`;
  `tools/api_reference.py`, `public_doc_inventory.py`, `ci_checks.py`, `ci_store_gc.py`,
  `test_reports.py`; `.github/workflows/ci.yml`, `.github/CODEOWNERS`; `justfile`; `README.md`.
- The model's gate codecs: `packages/belay-sqlite-model/Belay/Sqlite/Model/Codec/Source.lean`,
  `SourceExamples.lean`, the script record in `Codec/Resolution.lean`.

## Progress log

- 2026-10-21: ADR 0021 and the task file, from a survey of the dependencies on the product. The
  SQL text task now depends on this task and serves the harness only.
- 2026-10-21: review of ADR 0021 and the task: one finding, in the SQL text task (the harness
  also reads each statement's end, in `native_trace.py`); fixed. The second review had no findings.
- 2026-10-21: baseline before the removal: the judge's predictions are kept in
  `build/baseline-predictions`; the conformance runtime's closure is 3,727 MiB; `just test-full`
  passes (636 host tests, the Nix suites cached, 1 min 54 s).
- 2026-10-21: the conformance runtime is the runner's outputs only, with no verifier library or
  gate program (closure 3,245 MiB). The restriction examples run through `conformance-runner
  --predict`, without the foreign key scope of a corpus case, so that the foreign key
  restrictions stay reachable. `lean_libraries` no longer requires `SqliteVerifier.olean`, and
  `requires_lean` no longer requires the proof checker. `just test-full` and `just test-nix`
  pass; the predictions are byte-identical to the baseline.
- 2026-10-21: the API reference and the documentation inventory start from the model package:
  doc-gen4 runs in the model's Lake environment, and the inventory's entry is
  `Belay.Sqlite.Model` (203 modules, complete; before, 211 with the 8 verifier modules). The API
  reference builds with 268 public modules. `just test-source` and `just test-nix` pass.
- 2026-10-21: the product is removed (ADR 0021 D1): the CLI, `bin/`, `packaging/`, `examples/`,
  the verifier library and the gate, their Nix files, suites (`atuin`, `bundle`, `cli`,
  `kernel`), host tests and fixtures, the `release` job, the archive steps, the bundle phase,
  `adr3-p1.yml`, the recipes `test-atuin`, `runtime-package` and `package`, the three product
  experiments, the product documents and the engineering brief. The model loses
  `Codec/Source.lean`, `Codec/SourceExamples.lean` and the script record, and `belay/sqlite/syntax.py`
  loses `script_record`. The CI scope `package` is now `full` (`test-full`, `test-nix`,
  `test-scheduled-checks` and the `mutants` job), and tags no longer start CI. The coverage
  catalog keeps only the documented claims; the axiom audit had only product theorems and went.
  `.github/CODEOWNERS` keeps the integrity lines. README describes the model, the evidence and
  the surface. The product-only ADRs (0002, 0003, the 0003 trust extension and component
  research, 0010 except decisions 7 and 9) say "Superseded by ADR 0021"; ADR 0008 "Where
  resolution runs", ADR 0011 decision 6, ADR 0016 D2 and ADR 0017 D2 and D6 are amended. Links
  from ADRs to removed files point at `main` d0b1d728, the last commit that has them.
  Search for dangling names (imports, paths, links, Nix attributes, recipes and documents of the
  removed parts) outside ADRs, plans, review records, reports, research notes and the frozen
  corpus manifests' source hashes: one hit, the S1 report's option table
  (`experiments/surface-s1/README.md`), kept as the record of the S1 comparison.
  Results: `python3 tests/docs_test.py`, `just test-full` (766 s, the Nix suites rebuilt),
  `just test-nix` and `just test-scheduled` (1,836 s) pass; the lock check evaluates to true and `just judge-lock` equals
  `integrity/judge.lock.json`; the predictions are byte-identical to the baseline; the
  conformance runtime's closure is 3,243 MiB (baseline 3,727 MiB).
- 2026-10-21: review of the removal: two must findings (R19), ADR 0006 and ADR 0007 still required
  the installed runtime, the archive, the trust boundary document and the installer tests; both
  now have a dated ADR 0021 amendment. ADR 0001 got the same update, from a search of the other
  ADRs; their other mentions of the product are dated observations, not requirements.
