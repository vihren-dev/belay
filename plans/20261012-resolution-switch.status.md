# Status: switch the verifier to Lean resolution, step 1b of ADR 0008

Created 2026-10-12. Status: IN PROGRESS.
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

## Remaining

- All outcome items of the task.
