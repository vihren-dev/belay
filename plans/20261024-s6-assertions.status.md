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
