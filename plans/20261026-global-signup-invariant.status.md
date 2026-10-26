# Status: global signup invariant

Created 2026-10-26. Status: DONE (2026-10-26).
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
- 2026-10-26: commit 2 (`refactor:`): docstrings say that the output collation applies to the result-column
  number and that a non-calm filter is excluded by the premise, not covered.

## Reviews

- `20261026T171103Z-f5bfc2f7` (commit 1): two R2 musts, both fixed in commit 2.
- `20261026T171344Z-c73d1de5` (commit 2): no findings.

## Nix results (acceptance evidence)

- Predictions: `nix-build integrity/judge.nix -A predictions` gives
  `/nix/store/x9pb5pqq1s3s7mz7skixc4i3plsxp9nk-sqlite-verifier-predictions`; `diff -r` against the base
  `/nix/store/gbis3y12hpnbkhs0ja8f7ljym19gc149-sqlite-verifier-predictions` is empty (55 files, byte-identical).
- `just test-full`: exit 0, `/nix/store/5b0ralv5m5m1mgqzkzbp2bq6lm9vzbvd-sqlite-verifier-test-reports`
  (group counts passed: 481, 18, 28, 287, 153, 23, 3, 117, 233, 368, 41; the 368 include the new native
  check `test_filtered_duplicate_key_query_agrees_with_native_sqlite`).
- `just verdict`: exit 0, `/nix/store/nd13p9s3yj2dyj8y768hbppbxyxwxxm1-sqlite-verifier-verdict`
  (55 corpora, AGREE 5170, MODEL_UNSUPPORTED 2430).
- `just test-nix`: 71 passed, exit 0 (log `build/agent-logs/test-nix-2.log`). The first run failed with one
  error in `test_failed_pytest_target_has_no_output`, caused by a symlink loop that this session had made in the
  untracked `packages/belay/.lake/build/lib/lean` for a local runtime root; the loop was removed and the rerun is clean.
- `just test-scheduled-checks`: exit 0, 49 passed,
  `/nix/store/y4hd40ajgf3yr8ygg8kaj7gbzfyp4sw5-sqlite-verifier-scheduled-check-reports`.

## Integration on the open PR stack (2026-10-26)

The owner asked for one PR stack. The branch now has the merge
`merge: restore-dropped-task-files into global-signup-invariant for one PR stack`
on top of the possible write executions (#271), editor part 2b (#272), the
foreign-key done mark (#274) and the task-file restore (#276). The one conflict
was the module list of `packages/belay-sqlite-model/lakefile.toml`; it keeps the
modules of both sides. Checks on the merged tree:

- `just test-full`: exit 0, `/nix/store/zm2m11y8bczn1x2amym44hcwxqvfb6yj-sqlite-verifier-test-reports`.
- `just verdict`: exit 0, `/nix/store/x97krih71g1raag5g0jhlfnyx2ffl21l-sqlite-verifier-verdict`
  (55 corpora, AGREE 5170, MODEL_UNSUPPORTED 2430, as before the merge).
