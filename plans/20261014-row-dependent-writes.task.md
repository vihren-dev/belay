# Row-dependent writes, slice 3b of ADR 0012

Created 2026-10-14. Status: DONE (pull requests #115 and B).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Amendment 1:
Row-dependent writes (slice 3b)", with the owner decisions of 2026-10-14. Related:
slice 3a ([task](20261014-writes-with-output.task.md)), the restriction registry
([task](20261014-restriction-registry.task.md)), ADR 0011 for claims.

## Pull requests

As for slices 1 to 3a:

- **Pull request A (subject):** model, resolution, proofs, frontend mapping,
  restriction registry changes, authored coverage cases, mutants, obligation mutants
  and boundary cases, corpus writers. No change under `judge/` or `integrity/`.
- **Pull request B (judge, owner approval):** the coverage corpus of this slice and
  the obligation boundary corpus are frozen and claimed; cases that newly agree are
  added to `mustAgree`.

## Outcome

1. **Store-time affinity.** A Values-level `storeValue : Affinity → Value → Value`
   gives the value that SQLite stores for each affinity and storage class, by the
   rules of the amendment's table (a port of `applyAffinity`,
   `applyNumericAffinity`, `alsoAnInt` and `sqlite3VdbeIntegerAffinity` of 3.51.0).
   It is not `castValue`. INSERT values, defaults and UPDATE values are stored with
   it. A value that the affinity converts is no longer a model restriction; REAL
   values can be written to columns that are not keys.
2. **Row-dependent UPDATE.** `SET` values are any expression of slices 1 and 2 over
   the table's columns, evaluated on the old row of each selected row. The `WHERE`
   filter is any condition of slices 1 and 2; a row is selected when the filter is
   true, not when it is NULL or false. There is one resolved `update` form; the
   literal update of slice 3a is its special case.
3. **Errors and output.** Prepare errors in `SET` and `WHERE` (`no such column`,
   `misuse of aggregate function`) as in `SELECT`. NOT NULL and unique failures keep
   the input database. The change count is the number of selected rows. `RETURNING`
   reads the new rows.
4. **Restrictions.** A row-dependent `SET` value for a key column is a model
   restriction. Key values stay integers or NULL; key columns stay INTEGER, NUMERIC
   or BLOB. The registry, its documentation table and its examples change with the
   restrictions: a restriction that this slice removes leaves the registry, and the
   new one gets an id, a message and an example.
5. **Obligations and the verification target.** `insertReady` requires
   `storeValue a v = v` for each stored value instead of `lossless`. `updateReady`
   loses the filter conjuncts and keeps `tableReady` before the write and the key
   check after it. `Conforms` gains stored form: every cell equals `storeValue` of
   itself for its column's affinity. Every statement of the model keeps `Conforms`.
   `Contract.lean` does not change.
6. **Evidence.** Authored coverage cases with neighbors, as listed in the
   amendment's "Testing", agree with native SQLite and have kernel proofs. The
   mutants of the amendment each change a verdict. The obligation table of
   `conformance/obligation_mutants.py` matches the new obligations: each conjunct
   has a mutant and a boundary case, or names the restriction or the reason that
   covers it. The verdict counts of the claimed corpora do not go down.

## Tests

- Lean examples and proofs: `storeValue` for each affinity and storage class,
  including the 64-bit edges, whole REAL values, `2^53 + 1` and text that is not a
  well-formed number; `storeValue` is idempotent; for TEXT affinity its result is
  never a number. The update changes only selected rows at assigned positions and
  keeps rowids and order; the literal update is its special case. Every statement
  keeps `Conforms` with stored form. With constant key values, the check after the
  write agrees with row-by-row checks in every order.
- Frontend mapping of `SET` expressions over columns and of general `WHERE`
  conditions, with byte ranges, and refusal of the forms outside the slice.
- Authored coverage cases: the store-time list and the UPDATE list of the
  amendment's "Testing", including the slice 3a filter boundary case (`1.0` in a
  column without affinity under `c = 1`), which now must agree.
- Mutants of the amendment's list, each changing the verdict of a target case.
- The restriction registry, example and mutant link tests, with the changed
  registry; the obligation mutants in the scheduled suite.

## Key points for the implementer

- **One update evaluator.** `Resolved.Statement.update` now holds
  `List (Nat × Value)` assignments and an `Option (Nat × Value)` filter
  (`Resolution/Resolved.lean`), executed by `LiteralData.selected`, `assign` and
  `updated`. These change to `Resolved.Expr`; the query evaluator (`QueryEval.lean`,
  `truthy`) evaluates them. `Outputs.lean` computes the `RETURNING` rows of an
  UPDATE with `selected` and `assign`; it must use the same functions as the
  execution, or the two can disagree.
- **Proofs follow the structure.** `LiteralPreservation.lean`, `UpdateRules.lean`,
  `RowSpec.lean`, `ErrorKinds.lean`, `Laws.lean`, `Preservation.lean` and
  `SqlExamples.lean` match on the update form and on `lossless`. `Conforms` is in
  `Model.lean`, which is not owner-reviewed, but `Contract.lean` uses it by name, so
  its meaning changes for users; its plain-words docstring must say so.
- **Stored form must hold for every reachable database.** An invariant may join
  `Conforms` only if SQLite's write path guarantees it (owner decision on question
  5). The model defines no notion of databases reachable by its own statements.
- **`storeValue` is not `castValue`.** `CAST('abc' AS INTEGER)` is 0, but INTEGER
  affinity keeps `'abc'`; `sqlite3VdbeIntegerAffinity` excludes the least and
  greatest 64-bit integers. A REAL column stores a whole REAL as an integer on disk
  and reads it back as REAL; the model stores the REAL. Slice 2 has `atof`,
  `atoi64`, `realToI64`, `realSameAsInt` and `realText`.
- **Kernel cost.** Float operations are kernel-evaluable but slow (about 5 ms each);
  keep coverage cases small.
- **Registry and obligation table.** `affinity-conversion`, `real-value` in writes,
  `column-in-value`, `non-integer-filter`, `filter-form` and `literal-comparison`
  change or leave (`Resolution/RestrictionText.lean`,
  `conformance/restriction_examples.py`, `docs/semantic-subset.md`).
  `conformance/obligation_mutants.py` names `lossless` and the filter conjuncts; the
  boundary case `update-filter-real-equals-integer` of
  `conformance/authored_obligations.py` moves to the coverage cases, because the
  model must now agree on it. Corpus 10 is not claimed yet, so it can change.
- **Re-examine `tableReady` in `updateReady`.** In slice 3a it adds nothing to the
  key check after the write, given the key-value restriction and SQLite's
  constraints; the owner chose to keep it (2026-10-14). Check whether this still
  holds with row-dependent values in other columns, and record the result in
  `COVERED_ELSEWHERE["update-table-ready"]`.
- **Mutant anchors.** The text anchors of `write_mutants.py`, `query_mutants.py` and
  `obligation_mutants.py` that name the changed code must be updated, and their
  `GUARDS` must still name the declarations that contain them.
- **File size.** `Resolution/Writes.lean` (174 lines), `QueryEval.lean` (159),
  `SqlExecution.lean` (153) and `Arithmetic.lean` (160) are near the limit; put
  `storeValue` and the new rules in new modules.
