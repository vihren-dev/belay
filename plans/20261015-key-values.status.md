# Status: key values (slice 5a)

Created 2026-10-15. Status: IN PROGRESS.
Task: [task](20261015-key-values.task.md).
Specification: [ADR 0012, Amendment 4, "Key values (slice 5a)"](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/LiteralData.lean`, `RowUpdate.lean`,
`Comparison.lean`, `LiteralPreservation.lean`, `WritePreservation.lean`,
`Resolution/KeyDomain.lean`, `Resolution/Writes.lean`, `Resolution/Updates.lean`,
`Resolution/Restrictions.lean`, `Resolution/RestrictionText.lean`,
`conformance/obligation_mutants.py`, `conformance/authored_obligations.py`,
`conformance/restriction_examples.py`, `docs/semantic-subset.md`.

## Progress

- 2026-10-15: Amendment 4 accepted (#131, with owner decision 4: two key slices); task
  and status files created. Native 3.51.0 checked for key equality of TEXT, REAL,
  NUMERIC and untyped keys, composite keys with NULL, and NOCASE keys.
- 2026-10-15: the model: `LiteralData.keyCellsEqual` compares stored key cells with
  `compareValues`, never for NULL; `keyEqual` uses it for every key column. The key
  conjuncts of `insertReady` and `updateReady` (`comparisonReady`, integer-or-NULL key
  values) leave `statementReady`, and `tableReady` keeps only `constraints`.
  `Resolution/KeyDomain.lean` and the restrictions `key-affinity` and `key-value` are
  removed. Proof `keyCellsEqual_integer`: for integer cells the equality is the integer
  equality of before. Lean examples in `KeyExamples.lean`.
- 2026-10-15: the obligation mutants: no conjunct of `statementReady` can be violated by a
  native state after resolution any more, so `conformance/obligation_mutants.py` keeps
  its conjunct table with a reason for each, its mutant tables are empty, and the
  scheduled suite `obligations` and its test are removed. The boundary cases of corpus 10
  now describe states that the model handles (they should agree in the verdict).
- 2026-10-15: 17 authored cases (`conformance/authored_keys.py`, all AGREE, also the TEXT
  primary key that accepts two NULLs), five mutants (`conformance/key_mutants.py`, in
  the query and number measurement), and the corpus 17 writer. Tests that relied on the
  key restrictions follow the new rule: the REAL values of an INTEGER key in
  `conformance_generation_test` and the text cell of an INTEGER key in
  `conformance_pipeline_test` agree, one more legacy authored case agrees
  (`conformance_authored_test`), and the row-write mutant `no_store_of_constants`, which
  only the key-domain check could notice, is removed as an equivalent mutant.
- 2026-10-15: review of the slice commit (1 must, 1 should, fixed): `keyCellsEqual` has
  no catch-all match; the `resolveUpdate` docstring names the remaining restrictions.

## Remaining

- CI time, PR A; then PR B (claim corpus 17, `mustAgree`).
