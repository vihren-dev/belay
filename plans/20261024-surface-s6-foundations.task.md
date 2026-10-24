# S6 foundations: checked prototype and design findings

Created 2026-10-24. Status: OPEN. This task does not complete S6 or publish its API.
Status: [status file](20261024-surface-s6-foundations.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), D1 and Alternatives;
the target `model-user-guide.md` in `vihren-dev/sqlite-verifier-product`, commit
`1fa2cb081974552cacd61beea156e52066bf2af7`, questions 2, 4, 11, 12 and 13.
The guide's S6 semantics and outstanding decisions are restated below.

## Why this task is needed

ADR 0017 explicitly requires a prototype of `Std.Do` integration before S6.
The guide wants triples over every complete environment and every permitted
query result, with program continuations allowed to depend on those results.
It also wants equivalence to compose under script append and monadic bind.
Comparing only a canonical run or only the final visible database cannot be
assumed to give those properties. S4 supplies the monad/run laws and universal
success semantics; this task must reuse their final implementation.

The prototype starts after S4 part 2's interfaces are available. It can proceed
while S5 and model prerequisites are implemented, in a separate workspace with
disjoint files. Its findings inform the full S6 task and the owner's decisions.

## Required outcomes

- A small compiling prototype demonstrates `Std.Do.WP` and `WPMonad` for the
  existing `Sql` program type under Lean 4.34.1, or gives a concrete minimal
  failure showing why the intended instance cannot work. It proves pure/bind
  composition and a soundness connection to the existing execution semantics.
  A class instance alone is not that soundness connection. Demonstrate a triple
  both through the available `mvcgen` integration and through explicit checked
  lemmas, so the owner can assess dependence on the experimental tactic.
- The prototype's semantics cover every complete environment and every result
  branch of `Output.oneOf`, including data-dependent continuations. They retain
  connection settings, counters, the statement index and transaction snapshots
  across bind. Neither a new environment at each step nor a single canonical
  execution may stand in for that quantification. Errors and unmodeled outcomes
  have explicit meanings, consistent with S4 `Succeeds`; the guide's `ifOk` and
  `andOk` must not turn a model restriction into a successful proof.
- An equivalence audit tests the guide's current definition: equal return values
  and outputs, plus equal observations of the final databases by read-only
  queries. Identify precisely which hidden-state or execution-context facts a
  proof of append/bind congruence additionally needs, or prove none are needed.
  Examine counters, pragma settings, open transactions/snapshots, rowid and
  AUTOINCREMENT state, statement-indexed clocks, and permitted result branches.
  Give checked distinguishing examples when a proposed relation is too weak.
  Recommend the smallest adequate relation and convenient weaker observations;
  do not silently strengthen the public meaning of `≈`.
- The `before`-schema audit establishes what is missing to run a read-only
  postcondition over the fixed start and final database. The guide wants
  `before.t` to read the start table in an ordinary SQL query, including EXCEPT.
  The current model has no ATTACH. Describe the least additional semantic work
  needed for exact name resolution, metadata and query evaluation, and whether
  it belongs to the model or a proof-only context. No production implementation
  of a second database or ATTACH is part of this prototype.
- The footprint audit identifies which existing contracts can express reads
  and writes needed by statement commutation. Include foreign-key parent/index
  dependencies, triggers, counters and transaction effects. For a program whose
  next call depends on a result, demonstrate why a statement-local contract is
  sufficient or what additional all-continuation premise is necessary. Avoid
  a general effect framework unless the prototype establishes a concrete need.
- A concise design record gives the checked findings, remaining gaps and exact
  owner questions, with options and a recommendation for each. It distinguishes
  measured/compiled facts from a proposed design. The owner must decide changes
  to the guide's meanings before a full S6 task adopts them. No production
  semantics, public notation, dependency or judge claim changes in this task.

## Tests and acceptance

The bounded prototype compiles with the pinned compiler in an actual Nix-selected
fixture. Its checks include pure, bind, a result-dependent branch, a LIMIT tie
whose alternative branch fails, a supplied changing clock, a counter read after
a write, and transaction state carried into a continuation. Axiom audits reject
`sorryAx`, `ofReduceBool`, `_native` and assumed semantic soundness. Negative
examples refute the overly strong claim rather than merely failing to prove it.

Use current surface test support and finite timeouts. Do not create a second
interpreter or a full S6 implementation to conduct the experiment. Keep the
prototype isolated from production package imports; reserve shared manifests
before registering its fixture. Each coherent commit gets its relevant checks
and independent review. The one task boundary runs `just test-full`,
`just verdict`, `just test-nix` and `just test-scheduled-checks`, with the owner's
override recorded in [the build-boundary status](20261024-text-build-boundaries.status.md).
Frozen predictions and the judge lock remain unchanged. Only Nix results are
acceptance evidence in status files and PRs.

## Existing interfaces and constraints

The surface's `Program.lean`, `ProgramRun.lean`, `Env.lean` and S4's final
success/run laws are inputs, not APIs to replace during the experiment.
`ScriptRun.lean` and `SqlState.lean` in the model own connection settings,
snapshots, counters and execution transitions. `Env.clock` takes a statement
index. The final public `Run` is a presentation of execution, not necessarily
all state that a continuation can observe. The inspected compiler provides
`Std/Do/WP/Basic.lean`, `Monad.lean`, `Sound.lean` and triple/spec-lemma modules.

The full S6 task still needs ADR 0019 slices 4/5 and ADR 0022 slice 5. This
prototype does not substitute for their rebuild or FK proofs. Stop a dependent
branch and report a specification finding if any required semantic claim is
false; continue independent prototype checks while the owner decides.
