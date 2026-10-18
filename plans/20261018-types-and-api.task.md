# Invariants in types, API lemmas and position-free effects (ADR 0013, step 7)

Created 2026-10-18. Status: open.
Status file: [status](20261018-types-and-api.status.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), decision D8, D7
(`Statement.kind`), "Order" step 7, and the readiness results deferred from step 3.
Verdict: unchanged.

## Pull requests

Several pull requests in the stack, one for each part below that is self-contained. None
changes `judge/` or `integrity/`; `Contract.lean` and the approved files do not change.

## Outcome

1. **Expression errors in the type.** `PrepareError` splits into the errors that name a
   catalog object and the errors of an expression; `ValueIssue.prepare` carries only an
   expression error. A missing table of `FROM` reaches the statement's result without
   `ValueIssue`. `ErrorKinds.namesObject`, `IssueLemmas.lean`, `OperandIssues.lean`,
   `ReturningIssues.lean` and every `_issue`/`_issues` lemma do not exist; the prepare
   rules of `PrepareRules`, `DefinitionRules` and `UpdateRules` keep their statements.
   `PrepareError.message` gives the same text, and the JSON of the gate and the resolver
   is the same.
2. **No NaN real.** A `Value.real` cannot hold NaN: every real is built by `realValue`,
   or by a function that states why its result is not NaN, and `Table.Valid` states it.
   `isNull` and `isNullCell` are one function.
3. **Suffixes.** Proof files of `belay-sqlite` end in `Laws` (executable model), `Spec`
   (resolution) or `Examples` (`#guard` files); a package README states the meaning.
4. **API lemmas.** The library states `runSqlFrom_cons`, `advance_effect`,
   `effect_createTable_ok`, `effect_addColumn_ok`, `effect_write_ok`, a frame lemma (a
   write to position k leaves every other position unchanged) and
   `VerificationConditions.ofSchemaProjection` for schema-only scripts. The
   demonstrations of `sqlite-verifier` and the proofs of `examples/` use them and no longer
   unfold `runSql`, `runSqlFrom`, `advance`, `literalStep` or `step`.
5. **Position-free effects.** A statement's effect returns `Except` without a position;
   the script level adds positions to make an `Outcome`. One publication path applies the
   constraint checks, the ABORT, FAIL and ROLLBACK algorithms and the transaction state;
   `LiteralData.failedDatabase` does not exist.
6. **Readiness returns results.** The support check of a write or query and its execution
   compute the write or the query run once; `statementReady` reads that result instead
   of recomputing `inserted`, `updated`, `upsertRow` or `Query.run`.
7. **`Statement.kind`.** One classifier of the statement forms; `isControl`, `nonControl`,
   `SchemaOnly`, `NoWrites` and `prepareError?` classify through it.

## Tests

- `just test-full`, `just test-nix` and `just test-scheduled` pass after each part; the
  scheduled mutant suite kills every mutant, with anchors moved.
- The verdict of every corpus is unchanged, entry for entry, against step 6.
- `#guard` examples: the message of each kind of prepare error is the same text as
  before; the API lemmas used on a two-statement script.

## Key points

- **The JSON of `PrepareError`** is derived (`Codec/Resolution.lean`, `ScriptIssue`);
  a nested type changes its shape. The gate (`GateInputs.lean`) and the resolver
  (`verifier-gate/Resolver.lean`) write it. Keep the wire format, or write the instance
  by hand.
- **Direct `.real` constructions**: `StoreValue.lean`, `Resolution/Values.lean`,
  `Resolution/ReadDefaults.lean`, `Json/SqlValue.lean`, and examples.
- **`Value.isNull` treats NaN as NULL** through `rank`; with no NaN the two null tests
  agree.
- **Unfolding users**: `Demonstration.lean`, `ReverseDemonstration.lean`,
  `FailureDemonstration.lean`, `examples/constant_default/Proofs.lean`,
  `examples/missing_required_column/Proofs.lean`, `examples/atuin/AtuinFacts.lean`.
- **Effects**: `checkedWrite`, `insertOutcome`, `LiteralData.upsertRun` (its error carries
  the reached table), `SqlState.failed` and `SqlState.finish`; laws in `Laws.lean`
  (`literal_cases`, `statement_atomicity`, `constraint_rollback`) and `StepCatalog.lean`
  restate on the new effect.
- **The harness** (`VerifierConformance/Outputs.lean`) recomputes writes for its outputs;
  it may read the effect's result instead.
