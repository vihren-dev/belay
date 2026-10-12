# Switch the verifier to Lean resolution, step 1b of ADR 0008

Created 2026-10-12. Status: IN PROGRESS.
Specification: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md),
all of "Decision" except the profile measurement, the error phase and the
coverage shard (step 2) and the query syntax (step 3); "Consequences"; and
"Cleanup after implementation", except the recorder items that step 2 owns.
Previous step: [step 1a](20261010-syntax-resolution-core.task.md), DONE.

## Owner decisions

- 2026-10-12: the database maps catalog positions to tables, the same keys as
  `Resolved`. Approved files still write table names; helpers look the name up
  in the literal catalog.

## Outcome

1. **Python maps, Lean resolves.** For `schema.sql` and `migration.sql`, the
   Python frontend gives `Syntax` statements and a table from statement index
   and node path to the byte range in the file. It does no name lookup, no case
   folding, no affinity or type-name rule, no limit check and no numeric
   conversion. Syntax without a `Syntax` constructor gives `UNSUPPORTED` with
   its byte range, as today.
2. **Starting catalog.** Lean resolves the schema statements in description
   mode against the empty catalog. A prepare error in the schema is an input
   error that names the statement; a restriction is `UNSUPPORTED` with the byte
   range of the node.
3. **Script.** Lean resolves the migration in execution mode against the
   starting catalog. A restriction refuses the request with `UNSUPPORTED` and
   the byte range of the node, before any proof. A prepare error stays in
   `resolved` at its position.
4. **Execution semantics on `Resolved`.** The database maps catalog positions
   to tables. Each table has a `CatalogTable` shape and rows. `Conforms` relates
   a profile, a catalog and a database; validity uses the profile's column
   limit, not a constant. `runSql` executes `List Resolved.Statement`; a
   prepare error is a failure at its position, with the error. The execution
   errors that resolution now decides (`tableExists`, `missingTable`,
   `columnExists`, `tooManyColumns`, `invalidDefinition`) are gone.
5. **Generated inputs.** The generated modules contain the profile as a
   `Profile` literal, the schema and migration `Syntax`, the starting catalog,
   `resolved` and the resulting catalog. A trusted compiled Lean executable
   computes the catalogs and `resolved` and writes them as literal terms.
   Python computes none of them.
6. **Gate.** The `.olean` gate and the bundle checker read the structural
   record (profile and `Syntax`), check that the compiled `Syntax`
   declarations equal it, run `resolve` again, and reject a request whose
   compiled catalogs or `resolved` differ from the result. The verification
   target uses the catalogs, `resolved` and the profile structure.
7. **Approved files and examples.** The approved requirement and
   interpretation files of each example use the catalog vocabulary. Their
   baselines are updated. Every example gives the same verdict as before.
8. **Conformance.** The structural case carries the schema and script as
   `Syntax` in a new format version. The runner resolves and then executes. A
   restriction is `MODEL_UNSUPPORTED`. Native tables are compared at the
   catalog position of their name.
9. **Cleanup.** The items of the ADR's cleanup list for the frontend, the Lean
   model, the generated inputs and gate, the harness comparison of Python
   statements, the Python tests and the documentation are removed or changed.
   The ADR's completeness checks hold, except for the recorder's forced column
   limit, which step 2 replaces with measured limits.

## Tests

- The existing end-to-end suites pass: the examples (`verify`, `prepare`,
  `verify-bundle`), the kernel gate, the CLI, the bundle tests and the
  installed-runtime tests.
- Gate tests: a changed `resolved`, starting catalog, resulting catalog,
  `Syntax` or profile declaration is rejected by both checkers.
- Lean source of computed values: a round trip from value to source to the
  compiled declaration, and rejection of a changed record.
- Python mapping tests: each admitted production gives the expected `Syntax`
  and positions; unknown syntax gives `UNSUPPORTED` with its range; a Lean
  restriction and a schema prepare error give their byte ranges.
- Conformance: the model, frozen-corpus and pinned-corpus suites pass. Any
  case whose verdict changes is listed in the status with the reason.
- Each removed Python test case of a resolution decision names its
  replacement: a proof, a `#guard` example or a conformance case.
- A test checks the ADR's cleanup conditions over the frontend and the model.

## Relevant source and constraints

- Frontend: `belay/sqlite/` (`translate.py`, `schema_syntax.py`,
  `schema_translate.py`, `sql_dml.py`, `sql_admission.py`, `sql_values.py`,
  `sql_model.py`, `structural.py`, `admission.py`) and `migration_check/`
  (`inputs.py`, `lean_inputs.py`, `prepare.py`, `bundle.py`, `contract.py`).
- Lean model: `packages/belay-sqlite/Belay/Sqlite/` (`Model`, `Declarations`,
  `Execution`, `SqlExecution`, `LiteralData`, the preservation and fact
  modules, `Laws`, `Codec`) and `SqliteVerifier/`. Gate: `GateCore.lean`,
  `ProofChecker.lean`, `BundleChecker.lean`. Harness: `VerifierConformance/`,
  `ConformanceRunner.lean`, `conformance/model_cases.py`,
  `conformance/native_replay.py`, `conformance/native_metadata.py`.
- `.github/CODEOWNERS` lists the gate, the codec, `Contract.lean` and
  `migration_check/prepare.py`, `bundle.py`, `baseline.py`: the owner reviews
  them. Review condition R8 applies to the target, the gates and the generated
  inputs; R16 applies to every check that claims to detect tampering.
- Catalog positions are stable in the first scope: no statement removes or
  renames an object, and ROLLBACK restores an earlier catalog. A new table's
  position is the end of the catalog, so `Resolved.createTable` carries it.
- Restriction paths: each step is the argument position of the constructor,
  then the list index. The Python position table uses the same convention.
- The literal terms are Lean source. The gate compares them with a new
  `resolve` run by definitional equality, so an error in the source printer
  rejects the request; it cannot change the target.
- The step 1a `ResolveContext.mode` decides what the execution semantics model.
  The semantics must cover exactly what execution mode accepts.
- CI time: the Lean builds grow by the new semantics and shrink by the deleted
  model. Kernel evaluation of `resolve` must not enter a proof or a build; the
  gate evaluates it compiled. Build times before and after are recorded in the
  status.
