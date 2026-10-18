# Execution carries the catalog (ADR 0013, step 2)

Created 2026-10-18. Status: DONE (pull request #160; no verdict changed, so no pull request B).
Status file: [status](20261018-execution-carries-catalog.status.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), decision D1, amendment 1,
"Order" step 2, owner decision 5. Related: [ADR 0011](../docs/adr-0011-product-trust-and-development-integrity.md)
(the code-owned files this step changes), [ADR 0006](../docs/adr-0006-model-boundary-and-execution-levels.md)
(execution levels).

## Pull requests

- **Pull request A (subject and contract):** the model, the contract, the gate, the
  examples with their rewritten approved files, conformance and the tests. It changes
  code-owned files (`Contract.lean`, `GateCore.lean`, `BundleChecker.lean`, `Codec.lean`
  if touched, `migration_check/compile.py`), so it needs the owner's code-owner review
  and the owner's approval of the new approved-file hashes. No change under `judge/` or
  `integrity/`.
- **Pull request B (judge, owner approval):** only if a verdict changes (amendment 1,
  "A verdict can change"). It lists every changed case and its native result.

## Outcome

1. **One schema truth.** The execution state is `Database` with fields `catalog` and
   `rows` (amendment 1). It derives `Repr` and `DecidableEq`, and so do `Outcome`,
   `SqlState` and `SqlTransition`. No stored structure holds a `CatalogTable` beside the
   catalog: `Table` is the view that `Database.table` builds.
2. **Shared catalog changes.** `Catalog.createTable`, `Catalog.createIndex` and
   `Catalog.addColumn` are the only code that adds objects or columns to a catalog. The
   resolver (`Resolution/Definitions.lean`) and `step` (`Execution.lean`) both call them.
   A theorem states that resolving a statement and executing it give the same catalog,
   proved from that sharing.
3. **Writes read the state.** `Resolved.Statement.insert`, `update` and `upsert` have no
   `keys` field, and `upsert` has no `policy`. Execution takes the keys
   (`Catalog.uniqueKeys`) and the catalog's conflict algorithms from the state's catalog
   at the statement's table. The statement keeps its own `INSERT OR` algorithm and its
   conflict clause targets.
4. **One classification pass over the state.** `VerifierConformance` observes the
   catalog and the rows from the execution state. `resolveStates`, `stateBound`,
   `observationState` and `databaseOf`'s copy of the shape do not exist. The prediction
   JSON (`Predict.lean`, read by `conformance/predict_render.py`) keeps its format.
5. **The contract (amendment 1).** `SoundRepresentation` takes no catalog;
   `VerificationConditions` takes no `nextCatalog`; `FailureRepresentation` has no
   `catalog`; `catalogRequirement` applies to the result database's catalog. The gate
   builds that target. `Generated.nextCatalog` stays a generated input. The docstrings of
   every changed proposition restate the new formula in plain words.
6. **Dead proofs go.** `AliasPreservation`, `UpdatePreservation`, `WritePreservation`,
   `UpsertPreservation`, `UpsertConforms` and `DeletePreservation` are deleted, with
   their `lakefile.toml` globs. Facts that a remaining file needs move to it.
7. **Examples.** The examples (`examples/*`), the demonstrations
   (`packages/sqlite-verifier/SqliteVerifier/*Demonstration.lean`, `Examples.lean`) and
   the kernel gate fixtures (`tests/kernel_gate/`) use the new forms. `next_bound`,
   `catalog_bound` and the hand-built catalogs after each statement are gone where the
   state now gives the catalog.

## Tests

- `just test-full`, `just test-nix` and `just test-scheduled` pass. The scheduled mutant
  suite kills every mutant, with anchors moved to the new code.
- The verdict (`nix-build integrity/judge.nix -A verdict`) has the same counts as the base
  on every corpus, or every changed case is listed in pull request B with its native
  result.
- New `#guard` or `decide` examples show: a script that creates a table and inserts into
  it reads its keys from the state; `ROLLBACK` restores the catalog and the rows; the
  resolver's catalog equals the executed state's catalog after each statement of a mixed
  schema script.
- `tests/shared_table_shape_test.py` is replaced by a test of the new invariant
  (`Database.Valid`), or removed if the theorem in outcome 2 makes it redundant; its
  docstring says which.
- Every example verifies through the gate (`tests/kernel_gate_inputs_test.py`,
  `tests/bundle_test.py`, `tests/cli_test.py`), and an unsound candidate is still
  rejected.

## Key points

- **Trusted base.** `Contract.lean` and the gate are the product guarantee (ADR 0011,
  decision 6). Change them only as outcome 5 says, and say each change in the pull
  request so the owner can review it.
- **Approved files.** `examples/*/approved/*.lean` are pinned in their `baseline.json`.
  Rewrite them, update the hashes, and list every changed approved file in the pull
  request. Their meaning must not weaken: an interpretation that bound
  `Generated.startCatalog` or `nextCatalog` in its invariant still binds it.
- **Index positions.** Catalog positions include index objects; `rows` has an entry for
  each object, and `Database.Valid` requires an empty entry at an index position.
- **Snapshots.** `SqlState.snapshot` holds a whole `Database`, so ROLLBACK restores the
  catalog with the rows. The resolver's `ResolveState.saved` must give the same catalog.
- **Kernel cost.** Example proofs use `decide +kernel` over concrete states. A
  structure with lists reduces, but check the time of the model suite against the base,
  and report it.
- **Mutation harness.** `conformance/mutation_check.py` concatenates a fixed list of
  modules and needs `def step` last in `Execution.lean`. The mutant files match exact
  source text; each moved line moves its anchor.
- **Readers of the shape.** `LiteralData`, `RowUpdate`, `Upsert`, `UpsertRun`,
  `QueryJoins`, `ModelFacts.Covers`, `Table.project`, `Library.observeTable`,
  `ApplicationKeys` and `Predict.nativeTableOf` read `table.shape`. With `Table` as a
  view most keep working; the writes that build a new `Table` write rows only.
- **Policy.** `insertPolicy` (`Resolution/Writes.lean`) mixes catalog algorithms with the
  `OR` algorithm, and the resolver's restrictions (`constraintAlgorithmUpdate`,
  `replacesDefault`) still decide from the catalog at resolution.
- **Outputs.** `VerifierConformance/Outputs.lean` runs `upsertRun` again for RETURNING;
  it reads the keys from the state too.
