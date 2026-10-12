# Status: switch the verifier to Lean resolution, step 1b of ADR 0008

Created 2026-10-12. Status: DONE (2026-10-12).
Task: [task](20261012-resolution-switch.task.md).
Specification: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md).
Previous step: [step 1a status](20261010-syntax-resolution-core.status.md).

Relevant files: `belay/sqlite/`, `migration_check/`,
`packages/belay-sqlite/Belay/Sqlite/`, `SqliteVerifier/`, `GateCore.lean`,
`ProofChecker.lean`, `BundleChecker.lean`, `VerifierConformance/`,
`examples/`, `tests/`.

## Findings

- Survey, 2026-10-12, on `main` `5feb549e`: about 4,000 lines of Lean outside
  `Resolution/` use the old model, in the core package, `SqliteVerifier/`, the
  gate, the harness and the examples (784 lines). About 115 files mention
  `Schema`.
- The `.olean` gate trusts the compiled `SqlInputs` from the Python emitter.
  The bundle checker builds `nextSchema`, `script` and `profile` from the
  structural record and trusts the record's `nextSchema`.

## Progress

- 2026-10-12: task and status files created in the jj workspace `adr8-step1`,
  from `main` `5feb549e`.

- 2026-10-12: baseline build times on `main` `5feb549e`, forced rebuild with
  `nix-build --check` in the sandbox, no other load: `modelPackage` 14 s,
  `leanRuntime` 15 s, `conformanceRuntime` 19 s, `publicDocumentation` 5 s,
  development test suites 146 s (all suites rebuilt in parallel, with
  `--keep-going`, because test logs are not bit-for-bit reproducible).
- 2026-10-12: commit `0ff6b34c`: `Resolved.createTable` and `createIndex`
  carry their catalog position; `Resolved.insert` and `update` carry the
  table's unique keys (`Catalog.uniqueKeys`: primary key, UNIQUE constraints,
  unique indexes). Review `20261012T104153Z-0ff6b34c`: no findings.
- 2026-10-12: commit `e77423a6`: `resolveRequest` (schema in description mode, then migration in
  execution mode; a schema holds only CREATE TABLE and CREATE INDEX),
  `PrepareError.message`, the codec for syntax, catalogs and resolved
  statements, the version 2 `RequestRecord`, and the Lean source of the
  generated modules (`leanTerm`, derived `Repr`). A build-time check
  elaborates the printed terms of a sample and compares them with the values.
  Review `20261012T104800Z-e77423a6`: one must finding (R5, a catch-all match
  in `firstPrepareError`) and four should findings (R1 version literal, R6
  application words in model docstrings, R11 only single terms checked). All
  fixed in the next refactor: the names are now `resolveSchemaAndScript`,
  `ResolvedScript`, `ScriptIssue` and `ScriptRecord` in module
  `Resolution/SchemaScript`, `scriptRecordVersion` names the version, and the
  build-time check elaborates both complete generated modules. Two more
  rounds (`601b4835`, `0b7cde81`) asked for Lean's diagnostics in the check's
  errors and a test of them; fixed in `0b7cde81`, `e7474a7e` and `d1eebfba`,
  whose review has no findings.
- 2026-10-12: the key-domain checks of `sql_admission.py` become model
  restrictions in `resolve` (`Resolution/KeyDomain`), as the ADR's cleanup list
  says: a write to a table with a unique key over a column that is not
  integer-comparable, and a write of a value other than an integer or NULL
  into a key column. Without them, such a script would fail its proof instead
  of being unsupported.

- 2026-10-12: the Python mapping from the parser tree to `Syntax`
  (`belay/sqlite/syntax.py`, `syntax_definitions.py`, `syntax_writes.py`,
  `syntax_expressions.py`, `located.py`), next to the old translation, which
  the switch deletes. `Located` keeps the byte range of each node in the same
  path order as Lean's restriction paths. Declared types follow
  `sqlite3AddColumn`: the raw `typetoken` span after `sqlite3Dequote`. Lean's
  `decodeScriptRecord` reads the Python record (checked by hand with a sample;
  the switch adds the automatic check through the resolver).
- Finding: the old schema translation accepted an index before its table
  (`tests/sql_fixtures.py` `RICH_BASELINE`). SQLite refuses that schema, and
  so does `resolveSchemaAndScript`; the switch reorders the fixture.

- 2026-10-12, the switch (in progress, one self-contained commit): the Lean
  model runs `Resolved` statements on a database keyed by catalog position
  (`Model`, `Execution`, `LiteralData`, `SqlExecution` and the proof modules
  ported); `Conforms` takes the profile and checks `Catalog.Valid` under its
  limits (`Catalog.Valid.mono` lifts a check under small limits). The target,
  the library, the engineering examples and all example files use catalogs;
  the demonstrations hold for every profile with enough columns. The gates
  resolve the record again (`GateInputs.lean`) and compare every generated
  declaration; `migration-resolver` writes the generated modules. All examples
  verify with the new pipeline (both profiles for the invoice and Atuin cases),
  and `prepare` with `verify-bundle` works. The harness Lean side (version 3
  cases with native catalog metadata) compiles.
- Findings: `resolve` continues after a prepare error, so the resulting catalog
  of the allowed-failure example contains the unreached table; the failure
  representation now uses the prefix catalog. `allowed_failure` approved
  requirements name `.prepare (.tableExists "audit")`. Approved files and their
  baselines change in `examples/approved`, `examples/allowed_failure/approved`
  and `examples/atuin/approved`.

- 2026-10-12, the switch, continued: the Python frontend resolution modules
  (`translate`, `schema_syntax`, `schema_translate`, `sql_dml`, `sql_admission`,
  `sql_values`, `sql_model`, `structural`, `admission`) and
  `migration_check/lean_inputs.py` are deleted; `profiles.wire_tag` is gone.
  `migration_check/inputs.py` builds the record, runs the resolver and maps a
  refusal to its byte range. The harness uses version 3 cases (statement syntax
  and native PRAGMA metadata, `conformance/native_metadata.py`); Lean compares
  the catalog after each statement (`VerifierConformance/Native.lean`). The
  mutants of `mutation_check.py` and the documents of the ADR's list are updated.
- Frozen evidence regenerated with the project tools, not by hand:
  `conformance/cases/*.json` by `just conformance --prove`, and
  `conformance/regressions/injected-literal-corruption/` by
  `conformance.regressions.freeze` with the same classification and resolution.
  Both moved to the version 3 case format. Owner review needed.
- Finding: the kernel proof of the 2,000-column fixture (`limit_before_duplicate`)
  times out (over 120 s): the kernel evaluates resolution and catalog validity
  over 2,000 folded names. It stays a recorded, compiled-only case
  (`model_cases.Case.kernel_proof`); the ADR's lowered-limit case replaces it in
  step 2, when the recorder and the case format carry profile limits. The other
  four fixtures are kernel-checked in about 2 s each.
- Finding: three authored validity boundaries (duplicate column, missing key
  column, reserved name) are SQLite prepare errors that resolution decides; they
  now agree with SQLite instead of being unsupported.

- 2026-10-12: commit `53e14988`: the switch. Review `20261012T123032Z-53e14988`:
  11 must findings. Five are R8 owner-review markers (target, `GateCore`,
  `ProofChecker`, `BundleChecker`, codec): deferred to the owner review of the
  pull request. Six fixed in the refactor `2050776f`: `step` no longer fails on
  a definition that is not plain (R7; `statementReady` excludes it and CREATE
  INDEX, and the guard `ModeledDefinitions` carries the condition into the
  support lemmas), `advance` matches each outcome constructor (R5), proof
  sketches for four library theorems (R3), `Covers.columnsPresent` moved into
  the model (R6), and a next step in the generated-declaration errors (R10).
- 2026-10-12: CI time after the switch, same method as the baseline, two
  samples of the development test suites, both against a new `main` sample
  of 151 s taken in the same hour: 180 s and 161 s. The suites that did not
  change took about 7% longer in the first sample, so the second sample is
  the better comparison: about 10 s more (7%). The cause is spread over the
  verification suites: each Atuin verification takes 2 to 4 s more (kernel
  checks of literal catalogs in its proofs, and one resolver run per
  verification). Lean builds, forced rebuild: `modelPackage` 18 s (main 14 s),
  `leanRuntime` 18 s (15 s), `conformanceRuntime` 24 s (19 s),
  `publicDocumentation` 7 s (5 s). One sample each, under the same load as
  the 180 s run. All suites pass.
- Finding: the conformance kernel proofs (`just conformance --prove`) evaluate
  `resolve` in the kernel, because the case classification resolves the
  recorded syntax. The task allows kernel evaluation of `resolve` in no proof
  or build of the verification path; these proofs are harness evidence. The
  2,000-column case shows the cost: it is compiled-only until step 2.

## Removed Python tests and their replacements

| Removed test (case group) | Replacement |
| --- | --- |
| `test_translation.py`: `transition` errors (table exists, missing table, column exists) | `Resolution/Examples.lean` `#guard`s; `PrepareRules`, `DefinitionRules` theorems; `cli_test.py::test_schema_prepare_error_names_the_statement` |
| `test_translation.py`: ASCII-only folding (`normalize`) | `Resolution/Examples.lean` folding `#guard`; `SqliteVerifier/Examples.lean` |
| `test_translation.py`: unsupported statement list | `syntax_mapping_test.py` refusals; restriction `#guard`s; `cli_test.py::test_restriction_names_the_refused_sql` |
| `test_translation.py`: parser failure classes, other grammar, grammar rejection, quoted text | moved to `sql_parse_test.py` |
| `test_schema_translation.py`: metadata and indexes survive ADD | `ModelProjection`, `SchemaExtension` theorems; Atuin example; `conformance_pipeline_test.py::test_catalog_comparison_catches_metadata_drift` |
| `test_schema_translation.py`: CREATE collides with an index, global namespace, aliases, missing key columns | `Resolution/Examples.lean` shared-namespace and rowid-alias `#guard`s; `NamesSpec`; `conformance_authored_boundaries_test.py` (SQLite prepare errors agree) |
| `test_schema_translation.py`: statistics tables, unsupported metadata | `Resolution/Examples.lean` `sqlite_stat1` `#guard`; `SchemaExamples.lean`; `syntax_mapping_test.py` refusals |
| `test_sql_writes.py`: write syntax, transactions | `syntax_mapping_test.py`; `TransactionSpec`; `SqlExamples.lean` |
| `test_sql_writes.py`: literal storage values, numeric conversion | `Resolution/Examples.lean` numeric `#guard`s; `generated_inputs_test.py` literal case |
| `test_sql_writes.py`: key domain, coercing writes, unique index update | `Resolution/KeyDomain` `#guard`s in `Resolution/Examples.lean`; affinity restriction `#guard` |
| `schema_generation_test.py`: profile equivalence, kernel properties | `Codec/SourceExamples.lean`; examples verified under both profiles |
| `generated_inputs_test.py`: emitter parity | rewritten: parity with the resolver output and tampered records |

- 2026-10-12: review `20261012T125454Z-2050776f` of the refactor had one must
  finding (R11: no checked example of `step` running a definition that is not
  plain). This was the second round with new must findings; the owner approved
  the fix. Commit `68ca1ab8` adds two kernel-checked examples
  (`SchemaExamples.lean`). Review `20261012T130540Z-68ca1ab8`: no findings.

- 2026-10-12: merged `main` `0adb73dc` (ADR 0010, ADR 0011 up to step 8) into the
  branch. ADR 0011's prediction path used the deleted translation, so the merge
  ports it: `VerifierConformance/Predict.lean` resolves the syntax and reports
  native catalog metadata, and `conformance/predict.py` and `predict_render.py`
  follow. The judge lock and the claims do not change. The verdict passes, with
  more agreeing cases than `main`: corpus-v1 9 (main 2), v2 15 (8), v3 31 (11),
  and no DISAGREE or HARNESS_ERROR. Review `20261012T132010Z-1370bc41`: one
  must finding (R5, a catch-all over default expressions), fixed in
  `18e8f83c`; review `20261012T132419Z-18e8f83c`: no findings.
- 2026-10-12: final CI time against the merged `main` `0adb73dc`, two rounds
  that alternate `main` and the branch, forced rebuilds: development test suites
  143 s and 143 s on `main`, 148 s and 149 s on the branch (+5 s, +4%);
  `modelPackage` 14-15 s to 17 s, `leanRuntime` 14-16 s to 16 s,
  `conformanceRuntime` 20 s to 22 s, `publicDocumentation` 5-6 s to 6 s. The
  verdict's prediction step takes 4 s on both. These numbers replace the
  earlier comparison against `5feb549e`.

- 2026-10-12: CI on PR #97 failed in `just package`: `test_nix_test_targets`
  replaces `tests/kernel_gate_test.py` with a failing stub, and
  `kernel_gate_inputs_test.py` imported its fixtures from that module. Fixed in
  `7588f379` (fixtures in `tests/kernel_gate_support.py`); review
  `20261012T180456Z-7588f379`: no findings. Locally all 65 `requires_nix` tests
  pass; `runtime-package` did not start, because the resource check found 9.85
  GiB free of the required 10 GiB, so CI runs it.

- 2026-10-12: owner comment on PR #97 about the added lines. 70,000 of them came
  from pretty-printed frozen cases; `main` stored them as compact JSON. Commit
  `cfd1a7ac` restores the compact form (same content) and makes the pipeline
  write it: the branch now adds 6,303 lines and removes 4,515. Review
  `20261012T181038Z-cfd1a7ac`: one should finding (a test of the whitespace),
  rejected. After an owner-approved cleanup (old `nix-shell` directories and a
  Nix garbage collection), all Nix suites and the `requires_nix` tests pass.
  `runtime-package` fails locally only because the local store path of
  `python3-3.14.7` was modified on 2026-10-09; it passes in CI.

## Remaining

- Nothing for this step. The five R8 findings wait for the owner review of the
  pull request. Step 2 of ADR 0008 replaces the compiled-only 2,000-column case.
