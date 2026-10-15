# Key values, slice 5a of ADR 0012

Created 2026-10-15. Status: DONE (pull requests #132 and B).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Amendment 4: Unique keys
and conflicts (slices 5a to 5d)", "Key values (slice 5a)", with the owner decisions of
2026-10-15 (#131). Related: slice 3a and Amendment 1 (the key obligations and
`rowDependentKey`); slice 5b (rowid aliases) follows this slice.

## Pull requests

- **Pull request A (subject):** resolution, execution, admission obligations, proofs,
  restriction registry changes, examples, authored coverage cases, mutants and a corpus
  writer. No change under `judge/` or `integrity/`.
- **Pull request B (judge, owner approval):** the coverage corpus (version 17) is frozen
  and claimed, and cases that newly agree are added to `mustAgree`.

## Outcome

1. **Equality.** Two rows conflict on a unique key when no key cell is NULL and each pair
   of stored cells is equal under SQLite's comparison with the BINARY collation
   (`compareValues`): numbers by value (`1` and `1.0`), TEXT and BLOB by bytes, and
   values of different storage classes never (`1` and `'1'`). This holds for INSERT and
   UPDATE, for single and composite keys, from `PRIMARY KEY` (other than a rowid alias),
   `UNIQUE` and `CREATE UNIQUE INDEX`.
2. **Restrictions.** `key-affinity` and `key-value` leave the registry, its documentation
   and its examples. `rowid-alias` (slice 5b) and `row-dependent-key` (Amendment 1) stay;
   a key column with a collation other than BINARY stays refused by the frontend.
3. **Obligations.** The admission conjuncts that require integer or NULL key cells
   (`comparisonReady` in `tableReady` and `updateReady`, and the key values of
   `insertReady`) leave `statementReady`; the conjuncts that remain keep their mutants or
   reasons in `conformance/obligation_mutants.py`.
4. **Verification target.** `Contract.lean` does not change; `statementReady` admits more
   states, and every admitted write still keeps `Conforms`.
5. **Evidence.** Authored coverage cases agree with native SQLite and have kernel
   proofs; each mutant below changes a verdict; the verdict counts of the claimed corpora
   do not go down (the boundary cases of corpus 10 for integer keys may now agree).

## Tests

- Lean examples: the equality for each storage class and affinity, composite keys, NULL,
  and a conflict within one INSERT and after an UPDATE.
- Proofs: for integer cells the new equality is the integer equality of today; the
  preservation theorems of INSERT and UPDATE keep holding.
- Authored coverage cases: TEXT keys that differ by case and that are equal; REAL keys
  with `1`, `1.0` and `'1'`; a key column without affinity with `1`, `'1'`, `1.0` and
  `x'31'`; NUMERIC keys with `'1.0'` and `1`; composite keys of mixed affinity with NULL;
  a duplicate within one INSERT; an UPDATE that makes and one that avoids a duplicate
  TEXT key; a `CREATE UNIQUE INDEX` key in the schema; `RETURNING` after a conflict.
- Mutants, each changing the verdict of an authored case: TEXT compared without case;
  values of different storage classes compared by value; integer and real never equal;
  NULL cells equal; one key column compared instead of all.
- The obligation, restriction registry, example, documentation and mutant link tests
  after the conjuncts and restrictions leave.

## Key points for the implementer

- **Equality.** `LiteralData.keyEqual` compares integer cells only; `compareValues`
  (`Comparison.lean`) is SQLite's comparison of stored values, which also treats two
  NULLs as equal, so NULL needs its own case.
- **Resolution.** `Resolution/KeyDomain.lean` (`keyDomainRestriction`) refuses non-integer
  key columns and values for INSERT (`Resolution/Writes.lean`) and UPDATE
  (`Resolution/Updates.lean`, which also has `rowDependentKey`).
- **Obligations.** `insertReady` and `tableReady` (`LiteralData.lean`), `updateReady`
  (`RowUpdate.lean`), and the proofs that use `integerOrNull` or `comparisonReady`
  (`LiteralPreservation.lean`, `WritePreservation.lean`). The obligation mutants and
  their boundary cases (`conformance/obligation_mutants.py`,
  `conformance/authored_obligations.py`, a scheduled suite) name the conjuncts by their
  text.
- **Stored form.** `Conforms` requires every cell in its stored form, so equality of
  stored cells is SQLite's index equality without further conversion.
- **Kernel and mutant cost.** Keep authored cases small; measure the mutant and model
  suites after the change.
