# Status: S6 fresh-run triples and assertions

Created 2026-10-24. Status: OPEN. Task refreshed 2026-10-25 and assigned for
implementation of part 1 in workspace `sqlite-verifier-s6-assertions`, based on
`e3baff02` (published PR #254, above the S6 execution contracts of PR #250).
Part 1 is in progress: the context observation unit is implemented (see Part 1
progress). Nix acceptance is not claimed yet; it is recorded at the end of the part.
Task: [task file](20261024-s6-assertions.task.md).
Specs: ADR17 S6; accepted fresh-run and explicit effect-premise decisions.

## Scope and inputs

The owner accepted an explicit fresh-run helper on 2026-10-24. Ordinary Std.Do
triples retain arbitrary contexts. The helper fixes the initial database,
complete environment, initial connection, index zero and empty trace. Existing
Holds retains its default observation; context-aware assertions have a separate
name. Before always refers to the captured start, including after bind.

Execution contracts are DONE (2026-10-25). The initial/current query task has
no implementation; it waits for the query-source and view work. The checked S6
prototype established the candidate transformer and soundness route, but
supplied no production assertions and no before-query semantics. The universal
guide examples need the accepted schema and trigger/FK conditions; native
trigger counterexamples remain required negative fixtures.

## Progress

- 2026-10-24: specified fresh/ordinary equivalence, observation distinctions,
  compositional rules and universal guide acceptance. Review
  20261024T152453Z-8687f111 found no musts and one naming should: the predecessor
  specifies conditional/total policies but does not prescribe helper names.
  This task now explicitly supplies ifOk/andOk over those policies. No
  implementation or Nix acceptance is claimed.
- Follow-up review 20261024T152713Z-33693f10 has no musts or shoulds.
- 2026-10-25: carried the reviewed task and status into the implementation
  workspace (commit "docs: carry the reviewed S6 assertions task").

## Readiness refresh, 2026-10-25

The readiness audit of 2026-10-24 (accepted `52cd08bf`) found no new owner
decision. The refresh against the production tree at `e3baff02` changed the task
as follows. It adds no scope and needs no owner choice.

- **Reuse list added.** The task lists `FreshTriple` and its four theorems,
  `Sql.andOk`/`Sql.ifOk` and their laws, `sqlWPMonad`, the triple soundness
  theorems, the `send`/`query`/`single` specifications and `Sql.Branch.valid`.
  These are complete. Remaining new work is fresh composition rules, assertions
  and their bridges, assertion-level `ifOk`/`andOk`, fresh notation, `#explain`
  coverage and the universal examples.
- **Counter and validity wording corrected.** Fresh entry uses
  `ExecutionContext.initial db env`, so it takes the supplied environment's
  counters; it does not force zero or default counters. The context stores a raw
  connection. The default assertion agrees with `Holds` under a validity proof of
  the visible database; `Sql.Branch.valid` gives it for the final context of a
  fresh run. No runtime validity test and no context field is added. Context
  observations use the actual clock at the next index, the actual counters, the
  settings and the connection, and discard the observed step's connection.
  Equality bridges must account for pragma settings as well as clocks and
  counters.
- **`#explain` is extended, not created.** The 2026-10-24 audit said that the
  task's mention of an existing explanation path was stale because only the guide
  promised `#explain`. That was true on the S4/S6-execution line. Migration
  patterns part 1 (PR #254, `MigrationExplainCommand.lean`) now provide the
  command for the four migration primitives. This task extends the same command
  to fresh-run triples, ordinary triples and `Succeeds`, as the guide
  promises (S4 deferred it to S6). Authorized by the owner's request; no further
  choice is needed.
- **Two-state assertions marked dependent.** The initial/current query
  context is unimplemented. The task marks every `before` outcome and fixture
  (two-state assertions, the purge frame example, `before` diagnostics) as
  depending on it, and keeps them in acceptance as part 1b. Part 1 and part 2 are
  otherwise as before.
- **Stale input text replaced.** The task no longer says that the production S6
  contracts are absent from the tree. The link to the before-context task file is
  now a plain reference, because that file stays in the planning workspace.
- **Success equivalence narrowed.** `FreshTriple.succeeds_iff` and
  `Sql.andOk_complete_iff` already prove the S4 bridge. The task asks only for
  the form in the new notation and the proof that `S succeeds where G` equals it.

Design decisions that the task leaves to the implementation, recorded when made:
names of the context-aware assertion, the fresh notation and the value-aware
`ifOk`/`andOk` variants.

## Part 1 plan (informal, one coherent unit per commit)

1. Context observation: the real-context output of a query, the default
   assertion, the context-aware assertion and their correspondence theorems.
2. Independence bridge and disagreement examples (clock, counters, pragma).
3. Fresh composition rules and use of ordinary triples inside a fresh run.
4. Assertion-level `ifOk`/`andOk`, assertion terms, fresh notation.
5. `#explain` for fresh triples, ordinary triples and `Succeeds`.

## Part 1 progress

Evidence below names local checks only as development steps. Nix acceptance for
the part is recorded in the closing entry.

- 2026-10-25, unit 1 (context observation): `Script.outputIn` is the public
  real-context output (the first output of the existing `runScriptFrom` from the
  context's clock, next index and connection; no second interpreter).
  `Holds.inContext` is the real-context assertion and `Holds.reached` the default
  assertion at a context (`Holds.inContext` at the context's default observation,
  `ExecutionContext.defaultObservation`). Proved: `Holds.reached_initial`,
  `Holds.reached_iff_holds(_of_valid)`, `Script.outputOn_eq_outputIn`, and the
  independence bridge `Script.outputIn_eq_of_independent` /
  `Holds.inContext_iff_reached` for resolved queries without clock or counter
  reads over equal databases. Modules: `ContextObservation`,
  `ContextObservationLaws`, `ContextObservationBridge`. Fixture
  `tests/surface/AssertionContexts.lean` (kernel): default and real-context
  assertions disagree on a clock read, on `changes()` after a write and, for the
  pragma setting query, on the observed outputs (`rows [[1]]` against
  `rows [[0]]`); the default assertion follows an open transaction and a
  rollback; the clock read depends on the next index; a default assertion does
  not imply a fresh entry. Test: `tests/surface_assertions_test.py`
  (registered in `tests/nix_suites.json`, suite `surface`).

- 2026-10-25, review of unit 1 (156fc263): four findings fixed in a refactor
  commit: the validity theorem states only what it proves, the clock-free step
  fact is proved inside its single user instead of as a model-only lemma in the
  surface (R6), the three modules have module docstrings, and this summary is
  current.
- 2026-10-25, unit 2 (fresh rules and assertion terms): `FreshTriple.pure_iff`,
  `bind_iff`, `mono`, `and_iff`, `of_triple` (ordinary triple at the initial
  context) and `bind_triple` (ordinary continuation specification inside a fresh
  run) in `FreshRules`. `AssertionTerms`: `ContextAssertion`, `holds` (default),
  `holdsInContext` (real context), `ifOk`/`andOk` and the value-aware
  `ifOkWith`/`andOkWith` as Std.Do postconditions, proved equal to `Sql.ifOk` and
  `Sql.andOk` (`triple_ifOkWith_iff`, `triple_andOkWith_iff`), `FreshEnsures` with
  the same equalities and `Succeeds.iff_ensures` (S4 success equals the fresh
  claim with `andOk ⌜True⌝`, by `Sql.andOk_complete_iff`). Fixtures
  `FreshAssertionRules` (pure bind keeps the start; consequence; conjunction; two
  steps and a nested specification keep the captured database and environment; a
  fresh claim is refuted as an arbitrary-context triple) and `AssertionPolicies`
  (prefix error and prefix unmodeled stop under both policies, error then write,
  error then unmodeled step, every `oneOf` choice, returned outputs, `holds` and
  `holdsInContext` as postconditions).
- 2026-10-25, review of unit 2 (8be7d23e): the consequence rule's docstring states
  its unrestricted premise, the fixture `alternateStops` names every `Value`
  constructor instead of a catch-all, and the new fixtures have module docstrings.
- 2026-10-25, unit 3 (notation and `#explain`): `program ensures post` and
  `program ensures post where query` elaborate to `FreshEnsures (Runnable.toSql
  program)` with the always-true or the `Holds` predicate; the guard query check
  uses the query's source position (`FreshNotation`). The existing `#explain`
  command (`MigrationExplainCommand`) now also explains `FreshTriple`,
  `FreshEnsures`, ordinary `Std.Do.Triple` and `Succeeds` claims
  (`ClaimExplanation`): entry assumptions, the captured start, the error policy
  recognized from `ifOk`/`andOk` or "neither", and the observation of `Holds`,
  `holds` and `holdsInContext`; migration messages are unchanged. The
  `ensures` notation must be parenthesized in a declaration signature, like the
  other claim notations. Fixtures `FreshNotationExamples` (expansions by `rfl`,
  `succeeds where` equals `ensures andOk ⌜True⌝ where`, negative diagnostic at the
  query) and `ClaimExplanationExamples`; `tests/surface_assertions_test.py`
  checks the messages and five negative diagnostics (query not one read-only
  statement in `ensures where`, `holds` and `holdsInContext`; unsupported
  proposition in `#explain`).
- 2026-10-25, review of unit 3 (71dee9bd): the error policy comes from the head of
  the postcondition itself, not from any constant in the claim (a negated or nested
  `andOk` is not reported as a policy); an ordinary triple is explained only for the
  `Sql` monad (a triple over `Id` is reported as unsupported); the recognized
  policy and observation names are named, documented lists.
- 2026-10-25, second review of unit 3 (3b563bca): an ordinary triple is explained
  only for `Sql` with the standard transformer `sqlWPMonad`; the fallback policy
  text no longer says that a postcondition must inspect the trace to reject
  errors.
- 2026-10-25, third review of unit 3 (d06b0d47): the transformer check requires
  the projection `WPMonad.toWP` applied to the constant `sqlWPMonad` itself, so a
  copy of the instance or an expression that only mentions it is not explained;
  `tests/surface_assertions_test.py` rejects an `Id` triple and a copied
  transformer and checks the fallback policy text.

## Part 1 acceptance, 2026-10-25

Source commit `05b1db63` (review 20261025T074937Z-05b1db63: no findings). Nix
results (shared settings max-jobs 1, cores 2; logs in
`build/agent-logs/s6-test-full.log` and `s6-verdict.log`):

- `just test-full`: exit 0, output
  `/nix/store/mqcib6r6a7y2g1wzwkz66ihilg4csgya-sqlite-verifier-test-reports`.
  Host source checks 472 passed (71 deselected, 49 subtests). Suites: corpora 54,
  documentation 12, frozen 153, harness 246, model 251, packages 3,
  parserLibrary 4, sample 23, surface 108, upstream 117, all passed. The ten
  cases of `tests/surface_assertions_test.py` are in the surface suite and passed.
  The public documentation inventory is part of the documentation phase.
- `just verdict`: exit 0, output
  `/nix/store/jvm10nn3zb4ibcnk41c4cqpplyg5i6fp-sqlite-verifier-verdict`; every
  corpus reports AGREE and MODEL_UNSUPPORTED counts only.

Part 1 is complete. Not done, by task design: part 1b (two-state `before`
assertions, which wait for the initial/current query context), part 2 (universal
guide examples, remaining frontend diagnostics, private guide integration), and
the task-end `just test-nix` and `just test-scheduled-checks`.

## Part 2 (universal examples and diagnostics), started 2026-10-25

Scope from the coordinator: universal examples and the remaining frontend
diagnostics that do not need the initial/current query context; no private guide
edit (the guide change is written down below); do not edit the views agent's
files (`tests/surface/DbBangErrors.lean`, `tests/surface/SuccessUniqueEmail.lean`,
the balance success fixture, `tests/surface_guide_test.py`,
`tests/surface_success_test.py`); new examples live in new fixture files and the
new test `tests/surface_assertion_examples_test.py`.

### Unit 1: insert then lookup over every database

- Library: `packages/belay/Belay/Sqlite/PlainInsertEffect.lean` (the fresh `ifOk`
  shape `Sql.ifOk_send_plainInsert` of a plain insert that is modeled) over the
  model laws in `packages/belay-sqlite-model/Belay/Sqlite/Model/PlainInsertEffect.lean`
  (the reached database of a plain insert) and `Model/PlainInsertRows.lean` (the
  inserted rows are the old rows plus one appended row; counting and membership
  laws). The model-only laws were first in the surface package and moved after
  the review of `ed9cb8b6`.
- Fixtures: `CustomerInsertSite` (the explicit `CustomerInsertSite` structure of
  schema, resolution, affinity and modeledness conditions, and the fresh
  reduction `insert_then_holds`), `CustomerInsertQueries` (the two lookup
  queries as row facts), `InsertLookupClaims` (universal theorems
  `inserted_customer_is_unique` and `inserted_customer_has_the_name`, a positive
  example, and kernel counterexamples: an after-insert trigger that removes the
  inserted row, a table without key (two customers share the id), and a `UNIQUE`
  name that makes the insert fail).
- Decision: the guide's single lookup query with two subqueries and the
  filtered GROUP BY invariant query are not supported by the model's evaluator
  laws (one subquery per statement), so the lookup claim is two supported
  assertions (exactly one customer has the id; one customer has the id and the
  name). Extending the evaluator is a model change shared with other agents.
- Decision: "the INSERT is modeled" is an explicit premise of the site (it
  depends on the database, for example the rowid bound). For concrete databases
  it is discharged for every clock and counter by kernel reduction.

### Unit 2: preserved count over every database

- Library: `packages/belay/Belay/Sqlite/SendSuccessIfOk.lean`. `Sql.ifOk_send_of_success`: a script that
  succeeds from the fresh start has every branch at the connection of the model run, with a valid database;
  `NormalizedFieldExpansion.ifOk_send_expansion`: for a `Site` of the lowercase-field expansion the
  reached database is `expandedDatabase`.
- Fixtures: `ExpansionCountQueries` (the count query holds exactly when the table has `n` rows) and
  `ExpansionCountClaims` (universal `expansion_keeps_the_customer_count` for every `n`, every pair of
  triggers and every bound values; the guide's `count_kept` is its instance for `expand`; instance on a
  database with two customers; counterexample: an `AFTER UPDATE` trigger that existed before the
  expansion removes the customers when the backfill fires it, so the database has no site).
- Decision: the premise of the claim is `(db.run expand).outputs.allOk = true`. The default-environment
  success gives success from every complete environment (`Script.allOk_env`), and a kernel evaluation with an
  open environment is too slow (about a minute), so the closed form is also what the kernel checks.

### Review of unit 1 (`ed9cb8b6`, review 20261025T092136Z-ed9cb8b6)

Three musts and three shoulds. Model-only declarations (`insertOutcome_ok`,
`plainInsert_database`, `Output.ofStep_insert_ne_oneOf`, `RunStep.continues(_iff)`,
`runScriptStep_insert_ne_oneOf`, the row, scan, count and comparison laws) moved to
`Belay/Sqlite/Model/PlainInsertEffect.lean` and `PlainInsertRows.lean` in the model package,
registered in its `lakefile.toml` (they are not in the umbrella `Belay.Sqlite.Model`; the surface
modules import them). The two simp proofs that used the surface-only `sql_simp` set now list the
model lemmas. The duplicate `LiteralData.generatedCells_plain` was dropped for the existing
`NormalizedField.generatedCells_plain`. The wording "complete environments" of
`Sql.ifOk_send_plainInsert` is corrected (it holds for every environment), and the counterexample
theorems got docstrings.

### Unit 3: invariant with a partial unique index, delete-trigger counterexample

- Library: `Model/PartialUniqueCount.lean` (model package):
  `Table.KeysUnique.countMatching_partial_le_one`, at most one stored row satisfies
  `guard AND column = value` when a unique key with a filter implied by the guard exists.
- Fixtures: `AccountSignupQueries` (the query `SELECT 1 WHERE (SELECT count(*) FROM accounts WHERE
  deleted_at IS NULL AND email = $f) <= 1` and its row-count form), `SignupInvariantClaims`
  (structure `AccountSignupSite`, universal `signup_keeps` for every email value `f`: a
  successful signup keeps at most one live account with that email; kernel examples for a new email,
  a live email that fails and rolls back with the invariant intact, a deleted account whose email is
  reused; counterexample `nullableUnique`: with an ordinary `UNIQUE (email, deleted_at)` two live
  accounts share the email), `PurgeTriggerCounterexample` (a delete trigger removes another
  customer's session: the session exists before, the delete succeeds, and it is gone after; without
  the trigger it stays). Tests: `tests/surface_assertion_examples_test.py`.
- Deviation: the guide's invariant query is `oneLive` with `GROUP BY` and a `WHERE` filter. The
  model's duplicate-key query law (`DuplicateKeyQuery`) supports only an unfiltered `GROUP BY`; the
  filtered form needs model query-resolution work owned by the views agent. The invariant is
  therefore stated per email value `f`. Quantified over all non-NULL values it is equivalent to the
  global invariant; it says nothing about live accounts with a NULL email (the guide's `GROUP BY`
  groups NULLs, while `email = $f` never matches NULL), so the equivalence needs a non-NULL email
  premise (for example `email TEXT NOT NULL`).
  Options: (a) keep the per-value form; (b) add a filtered duplicate-keys law later and restate
  `signup_keeps` globally. Recommendation: (a) now, (b) when the query context lands.

### Skipped for part 1b (they depend on the initial/current query context)

- The purge-frame claim `purge_frame` (reads `before`) and its NULL-aware `IS NOT 1` condition,
  with the nullable-parameter and non-numeric-text tests.
- Diagnostics about `before` (unbound `before`, `before` in a one-state assertion).
- Two-state assertions and fixtures; the universal positive purge-frame/delete-effect law (only the
  delete-trigger counterexample is done, because it needs one state).

### Guide change to make (not done here; the coordinator edits the private guide)

Sections: "Level 2/3 Triples", "Two states", "Invariants" and the complete example
(`addCustomer_adds`, `count_kept`, `purge_frame`, `signup_keeps`).

- Correction: "The triple covers every database of every schema" is false. A claim covers every
  admitted database that satisfies the stated conditions: the schema (columns, affinities, a
  rowid-alias id), resolution of the statement without trigger or foreign-key rules, that the
  statement is modeled, and for the invariant a partial unique index.
- A claim about a fresh run is a `FreshTriple`/`ensures` (entry state is the initial one) or has an
  explicit entry premise; a default `Holds` precondition in an ordinary triple does not tie the
  database to the run.
- Success: `ifOk` is conditional (it asks nothing of a failed run); `andOk` requires that the run
  succeeded and that the postcondition holds. `count_kept` uses `ifOk` with the site and the closed
  premise `(db.run expand).outputs.allOk = true`.
- The insert-and-lookup claim is stated as two supported assertions (exactly one customer has the
  id; a customer has the id and name), not one two-subquery query.
- `addCustomer_adds` (a program that uses a result) is a fresh claim with the `AddCustomerSite`
  premise: the guide's precondition "customers has a name column" (`pragma_table_info`) is too
  weak; a trigger that removes the new customer makes the program report success with no
  customer of that name. The site lists the table shape, the plain insert resolution, and that the
  model runs the query and the insert for every value that the query returns. The id is not
  computed (aggregate and rowid-bound reasoning is out of scope); the claim holds for every id.
- `signup_keeps` is stated per email value with the filtered count query, with the partial unique
  index `WHERE deleted_at IS NULL`; the ordinary nullable `UNIQUE (email, deleted_at)` is the
  counterexample.
- A successful trigger may remove the inserted row; a delete trigger may remove an unrelated row
  (two kernel counterexamples). Explain default versus context-aware assertions and `#explain`.

### Unit 4: remaining frontend diagnostics (no `before`)

`tests/surface_assertions_test.py::test_assertion_diagnostics_reject_unadmitted_input` has six
more cases, each checked at its source position with the real compiler output: an empty script, a
comment-only script, `PRAGMA foreign_keys = 1` (a set PRAGMA) all report that the script must be one
read-only statement at the assertion term; `$missing` reports the Lean variable at the `$`; a grammar
error is reported at the offset of the string; `EXPLAIN` reports the unsupported command wrapper at
the start of the SQL. Nix verification of these cases: pending until the Part 2 end gates. Not done: diagnostics for `before` (Part 1b).

### Unit 5: a program that uses a result (`addCustomer_adds`)

- Model package: `Model/SelectStepKeeps.lean` (a continued, non-error SELECT step leaves the
  connection as it was), and three laws in `Model/PlainInsertRows.lean`
  (`rowsAt_three_parameters`, `LiteralData.newCells_getElem?_of_plain`,
  `LiteralData.inserted_single_rows`).
- Belay package: `SingleStatementChecks.lean` (`check_single_of_statement`, `selectedValues`,
  `mem_selectedValues`, `not_error_of_single`, `connection_resolveState`).
- Fixtures: `AddCustomerQueries` (programs, `AddCustomerSite`, the lookup law), `AddCustomerClaims`
  (universal `addCustomer_adds`: `FreshEnsures` with the site as the entry condition, and
  `ok = true -> Holds.reached (customerNamed name) final`), `AddCustomerInstances` (`shopSite` with
  kernel-checked modeledness, the kernel run that adds eve, counterexample `removingTrigger`).
  Test: `test_added_customer_claim_over_every_database` with a 300 s timeout per module, because the
  kernel check of the modeledness of the insert for every environment takes about 40 s.
- Deviation: modeledness of the query and the insert is a field of the site. It cannot be proved
  for all databases, because the readiness of an insert depends on the id (a rowid bound and the
  stored form). Options: (a) keep it as a site field (kernel-discharged on concrete databases),
  (b) prove it from aggregate-max and rowid-bound laws for the query result. Recommendation: (a).
