# Global signup invariant: no two live accounts share an email

Created 2026-10-26. Status: DONE (2026-10-26).
Status: [progress](20261026-global-signup-invariant.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S6;
[S6 assertions task](20261024-s6-assertions.task.md), the outcome "Two-state and
invariant examples cover their real behavior", and its status section "Owner
decision on the global invariant (2026-10-26)";
[S4 task](20261024-surface-s4.task.md), the duplicate-key query laws.

## Purpose and boundary

The private guide states the signup invariant with one global query:

```lean
-- accounts (id INTEGER PRIMARY KEY, email TEXT NOT NULL, deleted_at TEXT,
--           UNIQUE (email, deleted_at))
def oneLive := sql r"SELECT 1 WHERE NOT EXISTS (SELECT email FROM accounts
  WHERE deleted_at IS NULL GROUP BY email HAVING count(*) > 1)"
def signup := sql r"INSERT INTO accounts (email) VALUES (:e)"
```

The S6 assertions task proved the invariant per email value
(`signup_keeps` in `tests/surface/SignupInvariantClaims.lean`, with the query
`atMostOneLiveAccountWithEmail f`). The owner decided on 2026-10-26 that the
per-value form stays the claim of that task and that the global form is this
separate task. It needs a filtered duplicate-key query law, its surface lemma
and a bridge from the partial unique index to "no two live rows share a key".

This task adds query laws and a surface fixture. It changes no SQL meaning, no
execution, no prediction, no corpus, no claim and no judge file.

## Required outcomes

- **The filtered duplicate-key query has a law.** A model law gives the output
  of `SELECT 1 WHERE NOT EXISTS (SELECT c FROM t WHERE w GROUP BY k HAVING
  count(*) > 1)` for a table `t` with a filter `w`, a grouping key `k` under a
  collation and a result column `c` (a column or the literal `1`): the
  statement returns its row exactly when no two different rows of `t` for which
  `w` is true have keys that are equal under the collation. NULL keys are equal
  here, as for `GROUP BY`. The laws state which filters they cover; at least
  `col IS NULL` for a column of the table. A filter whose evaluation can fail is
  not silently treated as false.
- **One definition of the duplicate-key query.** The unfiltered S4 query
  `Query.duplicateKeys` and the filtered one are one definition (the unfiltered
  query is the case without a filter) or one is proved to be the special case
  of the other. The S4 laws and their callers keep their meaning; no second copy
  of the grouping proofs exists.
- **Resolution is covered.** A law states how the statement resolves in a
  catalog where `t`, the columns of `k`, `c` and `w` exist, as
  `resolveStatement_selectOne_notExists_duplicateKeys` does for the unfiltered
  query, on the current resolver (after the model name trace).
- **The surface has the lemma.** A belay lemma, next to
  `Holds.iff_selectOne_noDuplicateKeys` (`packages/belay/Belay/Sqlite/DuplicateKeyQuery.lean`),
  states `Holds` of the filtered query in plain row terms. Its premises are
  facts that a user can check about a database (table, columns, filter form),
  not the query result.
- **The partial unique index gives the invariant.** A law states: if a valid
  database has a unique index on `t` with the key `k` under the column
  collation and the filter `w`, and the key column is `NOT NULL`, then no two
  rows for which `w` is true have keys equal under the collation. The
  `NOT NULL` premise is needed because the index treats NULL keys as distinct
  and `GROUP BY` does not. `Table.KeysUnique.countMatching_partial_le_one`
  (`PartialUniqueCount.lean`) is the existing per-value form.
- **The guide's global claim is proved.** In `tests/surface`, a theorem states,
  over every admitted database with a signup site and every email `e`: if
  `oneLive` holds and the signup runs without an error, `oneLive` holds after
  it. The site premises are those of `AccountSignupSite` plus `NOT NULL` of
  `email`; the premise is never the invariant of the final database. The
  per-value `signup_keeps` stays, because it needs no `NOT NULL` premise.
- **The counterexample stays.** With `UNIQUE (email, deleted_at)` and no partial
  index, a kernel-checked theorem shows that the global triple fails: one live
  account for `a@x` and the signup of `a@x` give two live accounts.

## Tests and acceptance

Kernel examples check the filtered query law on concrete databases: no live
duplicate, a live duplicate, a duplicate where one row is deleted (no
violation), two NULL keys among live rows (a violation for `GROUP BY`), and keys
equal only under `NOCASE` when the collation is `NOCASE`. The global theorem and
the counterexample are checked through
`tests/surface_assertion_examples_test.py` (`check_module_chain`, as
`test_signup_invariant_with_partial_unique_index` does), with theorem-dependency
audits that allow only the ordinary logical axioms.

Native SQLite checks the concrete query results that the kernel examples state,
with the existing native helpers of the surface tests (no new evaluator).

All prediction files stay byte-identical to the base (`nix-build
integrity/judge.nix -A predictions`, 55 files). Relevant mutants only, by name
with `-k`, if a touched module has a mutant guard.

One acceptance part: each coherent commit gets focused checks, dev-build and
independent review; after the last review, `just test-full` and `just verdict`;
at task end `just test-nix` and `just test-scheduled-checks`. Only Nix results
are acceptance evidence.

## Existing interfaces and tricky points

- Model: `DuplicateKeyQuery.lean`, `DuplicateKeyResolution.lean`,
  `DuplicateKeyOutput.lean` (about 470 lines in total, `filter := none` and the
  result column `1` are fixed in `Query.duplicateKeys`), `PartialUniqueCount.lean`,
  `SimpleResultsLaws`, `CountQueryLaws`, `SimpleSubqueryRun`.
- Surface: `packages/belay/Belay/Sqlite/DuplicateKeyQuery.lean`;
  fixtures `tests/surface/AccountSignupQueries.lean` (`liveCondition`,
  `resolveOperand_column_is_null`) and `tests/surface/SignupInvariantClaims.lean`
  (`AccountSignupSite`, `signup_keeps`, `nullableUnique`).
- The filter is evaluated per row before grouping; the grouping law then works
  on the filtered rows. The existing per-value proof shows how the index filter
  `liveCondition` matches the resolved `deleted_at IS NULL`.
- The guide's inner query selects `email`, not `1`; inside `NOT EXISTS` only
  the presence of a row matters, but the resolution law must cover the column.
- Parallel work: the table-rebuild agent owns the run, statement and admitted
  statement files of the model (`AdmittedCatalogStatement.lean` and similar)
  and INSERT SELECT. This task owns the duplicate-key modules, the new query-law
  modules and the two signup fixtures. Keep edits of the barrels
  (`Belay/Sqlite/Model.lean`, `Belay/Sqlite.lean`, the lakefiles) to added lines.
- The private guide is not edited here: the status file records the checked
  statement and its premises for the guide acceptance task.
- Files stay below 200 lines, with checked public docstrings, plain-words
  statements and proof sketches.
