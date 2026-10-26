# Status: S6 initial/current query context

Created 2026-10-24. Status: DONE (2026-10-25).
Task: [task file](20261024-s6-before-context.task.md).
Specs: ADR17 S6 and the checked foundations prototype.

## Evidence and prerequisites

The prototype confirms that before-qualified queries are rejected and that the
current evaluator has one database origin. The guide explicitly requires fixed
initial-database observations. A bounded read-only context supplies that behavior
through the existing model; a general connection attachment feature is unnecessary.

The query-source/CTE/view representation is complete (PR #255), so this task now
owns the resolver, evaluator and text-translator files for qualified sources. The
accepted S6 equivalence and universal guide-effect decisions do not change this
primitive's meaning.

## Native SQLite 3.51.0 findings that bound the first version

- `before.t.a` names a column of `FROM before.t`; `before.t.*` is a syntax error
  in SQLite, so the model gives no three-part star.
- A table alias hides the table name: `FROM before.t AS x` allows `before.x.a`
  and refuses `before.t.a`.
- `FROM t, before.t` makes an unqualified column of both tables ambiguous.
- `before.nosuch` is "no such table" at prepare time (an error, never an empty
  observation).
- Schema arguments of table-valued functions (`before.f(args)`) and references
  to `before` inside view and trigger bodies are refused, as are schemas other
  than `before`. A view of the initial database expands in the initial context.

## Progress

- 2026-10-24: specified exact origins, metadata/context propagation, conservative
  extension laws and native two-database observation tests. Await task review.
  No production change or task acceptance result is claimed.
- 2026-10-25: native findings recorded above and task text corrected (no three-part
  star; `before` in view and trigger bodies and in function sources stays refused).
  Design fixed: the initial database and catalog are optional trailing arguments of
  resolution and evaluation; `Resolved.Source.initialTable` reads the initial database;
  one dispatch (`usesSchema`) makes ordinary queries use the unchanged path.
- 2026-10-25, commit "model: read the fixed initial database through a before-qualified
  source": `Syntax.TableReference.schema`, `Expr.qualified ... (schema)`, `ScopeSource.initial`,
  `Resolved.Source.initialTable`, optional `initial` arguments of `resolveSelect` and of
  the evaluator chain (`QuerySource.join` to `resolvedStepOutput`); restriction
  `initial-database`; translator accepts `before` only. Checks: `just dev-build`,
  Nix predictions equal to the baseline (one reason text restored), `tests/syntax_*`,
  restriction tests. Local results are not evidence.
- 2026-10-25, commit "model: observe a query over the initial and the current database":
  `observeTwoState`, `resolveTwoState`, `usesSchema`, `Syntax.Statement.asQuery?`; laws
  `*_initial_irrelevant` and `*_current_irrelevant` from `QuerySource.join` to
  `resolvedStepOutput`; conservative extension `observeTwoState_ordinary`; kernel
  fixtures `TwoStateExamples` and `TwoStateViewExamples`; surface entry
  `Script.observeTwoState`; `tests/surface_two_state_test.py` (native differential
  oracle with the pinned sqlite3 and an attached read-only copy, mutation check, refusal
  checks, modeled write between observations, axiom audit). Names and rowid: the model
  refuses `rowid`, `_rowid_` and `oid`, so the rowid fixture reads the alias name.
  The native oracle finds unqualified names in an attached database when the main
  database lacks the table, which the model (correctly) does not; the cases keep a
  current table whenever they query an unqualified name.
- 2026-10-25, review of the first commit: four rounds, each with new "must" findings, all
  fixed except one "should" finding that is rejected with a reason. The fixes: `CREATE VIEW`
  with a `before` source is refused (`initial-database`) because SQLite refuses it; error
  text of a three-part column keeps the schema name; the expansion of an initial view does
  not tag a function call as `before`; examples for initial views, subqueries and
  `Scope.resolveSchemaQualified_below`. The review rule for four rounds applies: the
  owner decides how to continue before the second commit is reviewed.
- 2026-10-25, fix of review round 5 (`20261025T160157Z-51cd4134`): the function-name collision
  in initial views is refused with `initial-database` (the later resolution reads function
  calls in the current catalog; proper resolution there needs a per-query mark and is
  deferred); `InitialSourceGuardExamples` adds the regression, a three-part column fixture
  with `before.t.a` and the same-name `t`, and `CREATE VIEW` refusals for a direct source,
  a joined source and a subquery source. Native finding: a view over `pragma_table_info`
  in an attached database is refused by SQLite ("unsafe use of virtual table"); the merge
  review made the model refuse it too (see the integration entry).
- 2026-10-25, fix of the first review of the observation commit (`20261025T191255Z-83a4451f`):
  plain-words statements say "no source with a schema name"; `asQuery?` and
  `Resolved.Statement.readsInitial` list their constructors; proof sketches for the
  independence laws; docstrings for the fixtures; the native test is split into
  `tests/surface_two_state_test.py` and `tests/two_state_support.py`.
- 2026-10-25, the first `just test-full` failed in `tests/test_model_package.py` (fixture modules
  must be named as compiled examples; fixed) and in 13 surface tests (the premise
  `reference.schema = none` and the optional `initial` argument of `subqueryContext` shift
  the arguments of the fixtures in `tests/surface`; fixed in the fixtures). The failed log
  of the second run is `build/agent-logs/gate-full-2-failed.log`.
- 2026-10-25, gates on the tree of the commit "Record review results of the surface fixture
  update" (all through the Nix targets; paths are store outputs):
  - `just test-full`: passed. test reports
    `/nix/store/v68lj4lic229x9ahy3arsrdwbjya7yf2-sqlite-verifier-test-reports`.
  - `just verdict`: passed. `/nix/store/fb0n1z24ww009ks678zrbd2qvg8rjji4-sqlite-verifier-verdict`.
  - `just test-nix`: passed, 71 tests (pytest `requires_nix`).
  - `just test-scheduled-checks`: passed.
    `/nix/store/ifmfp2dvlz4pi3f0vy3xjc6wcnzjnd9j-sqlite-verifier-scheduled-check-reports`.
  - Predictions: `/nix/store/i80d2crp94q05llk5qgx61dac4hhmqd3-sqlite-verifier-predictions`
    against the baseline `/nix/store/764gd728p06g20x9kfq29c1vrmdgjhqf-sqlite-verifier-predictions`:
    53 files, 0 changed records.
- Open points (not blocking): a function call in an initial view that names a view of the
  current catalog is refused with `initial-database`, not resolved; a call of
  `pragma_table_info` or `pragma_foreign_key_list` in an initial view is refused too, as in
  SQLite; metadata compared is column names
  only; JSON codecs now include `"schema": null`; the oracle finds unqualified names in the
  attached database when the main database lacks them. Part 1b of S6 needs corpus cases
  for `SELECT ... FROM before.t` against an attached read-only copy.
- 2026-10-25, integration above editor part 2a (`91f640e4`, head of #264) as the merge
  "integrate: S6 before-context above editor part 2a". Four files conflicted textually
  (`build-support/tests.nix`, the model `lakefile.toml`, and the two plan files: both sides had added
  these plan files, the later version of this task is kept); the glob list and the surface suite inputs
  carry both sides. Every file that only one side changed equals that side. The review of the merge
  (`20261025T204905Z-a785218e`) had two musts and two shoulds, all fixed in two refactor commits:
  an initial view that calls `pragma_table_info` or `pragma_foreign_key_list` is refused with
  `initial-database` (named by `isPragmaTableFunction`), the current-independence laws state that
  pragma sources are excluded, `sourcesOf` lists the statement constructors, and the restriction
  text names the collision. The next review of the fix (`20261025T205905Z-2b1c403c`) has no findings.
- Gates of the integration (store outputs; the first `just test-full` stopped at the 1500 s build
  limit with no failed test, log `build/agent-logs/gate-ifull-timeout.log`, and passed on the
  one allowed rerun):
  - `just test-full`: `/nix/store/g4xaff8wqx5ia1p17y2ln3gix9sxwdv4-sqlite-verifier-test-reports`
  - `just verdict`: `/nix/store/q00llah7d6mmsdp58wjmg74yc91q0zqc-sqlite-verifier-verdict`
  - `just test-nix`: passed, 71 tests (no store output).
  - `just test-scheduled-checks`: `/nix/store/msv3w32r416z64rcm7vf5x4j1kr8lp4n-sqlite-verifier-scheduled-check-reports`
  - Predictions `/nix/store/r1aksjg6av55bcs82fnlard7gsqi5ndk-sqlite-verifier-predictions`: 55 files,
    identical to `/nix/store/2c56akphxc884accaa9piqwgyhg3bpbq-sqlite-verifier-predictions` of #264
    (`diff -r` finds nothing).
