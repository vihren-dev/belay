# Status: global signup invariant

Created 2026-10-26. Status: OPEN. Model, surface lemma, bridge law, fixtures and native check are in
the first commit; reviews and Nix gates are open.
Task: [task file](20261026-global-signup-invariant.task.md).
Specs: ADR 0017 S6; the S6 assertions task and its owner decision of 2026-10-26.

## Decisions

- 2026-10-26 (owner): the per-value `signup_keeps` stays the claim of the S6
  assertions task; the global form is this separate task, after the model name
  trace (merged in PR #270).

## Progress

- 2026-10-26: task specified on main after #270.

- 2026-10-26 (design): `Query.duplicateKeys` takes `(sources) (filter : Option Expr) (column : Expr)
  (name : String) (key) (collation)`; the S4 query is `filter := none`, `column := literal 1`, `name := "1"`.
  The S4 belay lemmas (`Holds.iff_selectOne_noDuplicateKeys` and the others, same statements and premises
  as before) are corollaries of the filtered ones (`Belay/Sqlite/FilteredDuplicateKeyQuery.lean`,
  `FilteredDuplicateKeyEmpty.lean`); there is one copy of the grouping proofs. `GroupTermResolves` (S4) is
  `GroupTermResolvesIn` for the result column `1`; `Resolved.keptRows` is the rows that `WHERE` keeps
  (`keptRows_none` for no filter). A filter is covered when it is `Calm` (`whereCalm` premise); a filter
  that can fail is not calm, so the premise excludes it; the laws do not cover it and never read it as false.
- 2026-10-26 (baseline): predictions before any change are at
  `/nix/store/gbis3y12hpnbkhs0ja8f7ljym19gc149-sqlite-verifier-predictions` (55 files).

## Checked statement of the global claim (for the guide acceptance task)

`signup_keeps_global` in `tests/surface/GlobalSignupInvariant.lean`:

```lean
theorem signup_keeps_global (e : String) :
    FreshEnsures (send (signupAccount e))
      (fun db => Holds oneLive db ∧ Nonempty (GlobalSignupSite db e))
      (ifOk (holds oneLive))
```

`GlobalSignupSite db e` is `AccountSignupSite db e` (the statement is a plain insert that the model runs for
every clock and counter; `accounts` has `email` and `deleted_at`; the catalog has a unique index on
`accounts` with the one key `email` under the collation of the column and the filter `deleted_at IS NULL`)
plus `emailCell.notNull = true`. `oneLive` is the guide query. No premise states the invariant of the final
database. The counterexample `unique_with_null_does_not_keep_one_live` (`UNIQUE (email, deleted_at)`, no
partial index) is kernel-checked. `one_live_iff` gives `Holds oneLive` in row terms. The per-value
`signup_keeps` is unchanged.

## Progress log

- 2026-10-26: commit 1: model generalization (`DuplicateKeyQuery`, `DuplicateKeyOutput`,
  `DuplicateKeyGroupTerm`, `DuplicateKeyResolution`), bridge law `Table.KeysUnique.keptRows_pairwise`
  (`PartialUniqueKeptRows.lean`), belay filtered lemmas, S4 lemmas as corollaries, fixtures
  `GlobalSignupInvariant.lean` and `FilteredDuplicateKeyExamples.lean`, native check
  `test_filtered_duplicate_key_query_agrees_with_native_sqlite`. Local checks only (dev-build, belay and
  conformance lake build, focused pytest with a local runtime root); Nix results come at the end.
