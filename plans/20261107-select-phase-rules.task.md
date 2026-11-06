# Compositional SELECT proofs: implementation of ADR 0027

Created 2026-11-07. Status: IN PROGRESS.
Audience: team. Status: [checkpoint](20261107-select-phase-rules.status.md).
Specification: [ADR 0027](../docs/adr-0027-compositional-select-proofs.md) (accepted by the
owner on 2026-11-07), its [acceptance contract](../docs/select-automation-acceptance.md),
[retirement inventory](../docs/select-automation-retirement.md),
[source map](../docs/select-automation-source-map.md) and
[semantic review cover](../docs/select-automation-review.md).
Investigation: [specification task](20261028-select-automation-spec.task.md).

## Required outcome

The three parts of "Meaning of completion" in the acceptance contract hold:

1. **Decomposition rules for every family.** Each SELECT phase that the model
   describes has public proved rules in the model package: sources and joins,
   expressions, WHERE, grouping (expression keys and the row of a group),
   aggregates, HAVING, projection, DISTINCT, ordering, the window, compounds,
   subqueries and the execution bridge. A rule is stated for every query that
   meets its phase's own premises, in the most general form that the proof
   supports. Each positive case A01 to A22 is proved, with a hint or manually
   where automation is not yet required.
2. **Automatic closure of the core set.** `sql_auto` closes A01, A02, A03, A04,
   A08, A10, A13 and A14 without a hint that proves the whole query.
3. **Empty required column.** Every file that the retirement inventory marks
   required is deleted with its callers migrated; every candidate is decided
   at assignment, and the status file records each decision and the reason
   for each candidate that stays; every retired claim is derived by an
   acceptance case or a retained rule with the same entry assumptions. A
   file is retired only after the cases of its "Acceptance cover" pass, for
   example `ColumnQuery.lean` after A19.

Observable behavior that users see:

- `Run.returnsResult Q` and `Run.returnsRows P` (ADR 0027 D2), each
  `Decidable` when its predicate is. The successful-result bridge of the
  acceptance contract holds for a script of one SELECT, including the proof
  that generated alternatives are nonempty.
- `Holds`, `Empty` and `Fails` are abbreviations of the observation
  predicates, with the same truth value as their current definitions on every
  query script and database; their decidable instances and the `check_query`
  argument stay.
- `sql_select` proves the goal forms of the acceptance contract ("Public
  claims and automation"); `sql_run` delegates the SELECT obligations of
  `Sql.check` goals and triples to it; `sql_auto` reuses it in its bounded
  search and adds a route for the conveniences.
- `attribute [sql_select_rule PHASE] name` registers a proved theorem under one
  of the thirteen phases of the acceptance contract, locally or globally;
  explicit hints run first in supplied order, then registered rules in
  qualified declaration-name order.
- Failures leave typed residual goals with a phase-specific explanation, and
  B01 to B11 hold.

## Test suite

The suite verifies the observable behavior above end to end:

- **A fixtures**: one Lean module per family group under `tests/surface/`,
  each a module of an existing Nix surface suite (R20), with universal
  theorems over symbolic databases, empty and populated valid witnesses for
  each schema premise, and the "required contrast" of each case as a proved
  counterexample or an exact refusal. The motivating invoices theorem appears
  twice: with `db.HasCatalog invoices` and with generic table and
  column-presence premises.
- **Automatic closure**: the core-set theorems are proved by `sql_auto`
  without a whole-query hint; each closure also elaborates from its offered
  explicit steps without `sql_auto`.
- **B fixtures**: residual goals and their explanations are checked as text
  (not only as a failure); budget exhaustion and cancellation restore the
  goal and its siblings; an invalid rule cannot create a kernel-accepted
  proof; an unrelated registered rule, a rule with an unresolved premise and
  a local registration outside its scope behave as the contract says;
  background checking (`#sql_check`) recognizes the new claim shapes (B10).
- **Program composition**: one theorem composes a write and a following SELECT
  with the new procedure (A21), and one end-to-end theorem is the abstract
  invoices theorem.
- **Axiom audit**: every fixture's `#print axioms` reports only the allowed
  logical axioms, as the existing `check_module_chain` harness checks.
- **Migration witnesses**: the `Holds`/`Empty`/`Fails` equivalences with the
  old definitions are proved once and deleted after their last contract
  change, with their Nix acceptance recorded (ADR 0025 D4 test lifetime).

## Existing code and tricky points

- The experiments `tests/surface/SelectAutomationPhaseRules.lean`,
  `SelectAutomationPhaseBridge.lean` and `SelectAutomationPhases.lean` are the
  first drafts of the projection, grouping, group-row, window, DISTINCT,
  alternatives and execution-bridge rules. They are membership rules; D1 asks
  for predicates over complete collections (counts, multiplicity, order), so
  the library also needs cardinality, permutation and order transfer rules.
- `records` fuses grouping, aggregate evaluation, `HAVING`, projection and sort
  keys (`QueryResults.lean`). A grouped scalar column reads `Query.groupRow`
  except for a column in `firstRowColumns`; an `.output` sort key reads the
  projected output. The model's group row is not a native guarantee where the
  plan decides it (issue #309); rules state the model's row.
- `Query.results` is a representative; `Query.possibleResults` is the set of
  permitted results, and `Output.ofResults` sorts and deduplicates them. A
  rule that needs every permitted result must quantify over
  `possibleResults`; `normalResult ∈ possibleResults`, `results` need not be.
- `Query.outputOn_clean` alone permits `.may` faults (B05). The execution
  bridge must keep `Query.described`, plain nested subqueries, no `.may`
  source or run fault, and the derived-source ending and certainty checks.
  `EvalContext.Quiet` does not give complete-row source certainty.
- `Holds` reads `Script.outputOn`, the run of `db.raw` with foreign keys off;
  `Database.run` reads `Sql.run` with an environment. `Script.query_outputs`
  relates them for a query. `queryResult` reads `.done` as `.ok []` and the raw
  `.oneOf` wrapper as its first result: the bridge needs the SELECT premise and
  the nonemptiness of generated alternatives.
- `ScalarNoFrom.lean`'s laws take a quiet statement (fallible functions
  allowed); a re-derivation under a calm premise loses that capability.
- `sql_run` (`SqlRun.lean`) applies `Sql.check_query_select`,
  `check_single_select` and `check_send_select`, leaving the `reached`
  obligation over every `OutputChoice`; the SELECT procedure starts from that
  obligation. `AutoSearch.lean` runs routes under `Check.withinBudget` with a
  shared allowance; nested phase searches must not replenish it.
- The resolution-shape laws (`*Resolution.lean`) stay: the ADR 0026 D3
  certificate does not give the resolution equation. A test that needs a
  resolution equation for a symbolic catalog uses them or `decide +kernel` on a
  concrete one.
- Retirement is per family and does not wait for automatic closure. Callers in
  `tests/surface/Claims*.lean`, the claims driver, assertions, explanations and
  migration patterns change no statement.
- Model-semantic changes found during proof work need their own
  specification and conformance evidence; this task adds proof rules only and
  changes no prediction, corpus or judge lock.
- Lean code limits: files under 200 lines, Verso docstrings with plain-words
  statements, proof sketches for library theorems; the
  [Lean simplification goal](../docs/lean-simplification-goal.md) needs the net
  line change recorded at completion.
