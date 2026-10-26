# Contextual preservation experiment

Audience: designers and reviewers. Base: `6413afe3ff50`. Date: 2026-10-26.
Production packages are unchanged. Local Lean runs are diagnostics; the design
status records the root agent's Nix acceptance check.

## Result and proposed boundary

One condition can take the existing execution arguments: clock, counters,
parameters, resolved statement, and database. No new context record, typeclass,
monad abstraction, or interpreter is needed. `Keeps` and `Conditions` in
`ContextCore.lean` use that predicate. The latter selects the actual clock
and `Counters.view` used by the raw runner, rather than all connection counters.

`run_keeps` proves preservation with one resolved-script induction. The complete
formulas of both `runSqlFrom_holds` and `runSqlFrom_holds_ready` are derived from
it in `old_plain_formula` and `old_ready_formula`. The unconditional formula
acquires no support premise. Ready preservation pairs the ordinary condition
with raw `runStatement.ready`.

`surface_run_keeps` proves preservation with one surface-script induction.
`old_surface_plain_formula` and `old_surface_derived_formula` derive the complete
old formulas of `runScriptFrom_holds` and `runScriptFrom_holds_derived` from it.
Neither raw nor surface experiment calls the old traversal or step preservation
theorems. Existing effect, snapshot, outcome, and connection transport lemmas
remain the foundation.

The four old-formula adapters, including their recursive conversions between
condition predicates, are experimental evidence only. They must not become
production compatibility APIs. Production migration replaces old condition
predicates and their callers. It leaves one preservation induction for each of
the two distinct runners.

## Surface obligation

`StepCondition` supplies the contextual predicate after successful resolution,
clock selection, and the state support check. It uses the selected clock value
and visible counters from the same state as execution. Missing resolution or
clock, and failed support, require no contextual predicate from this definition.

`ScriptObligations` guards each reached step's obligation by the current
`SqlState.Holds` property. That guard admits conditions derived from the current
invariant as well as conditions supplied explicitly by callers. The preservation
induction supplies the guard at each reached state. Constructing derived
obligations therefore does not require a second proof that execution preserves
the invariant. States without the property impose no head obligation.

The two runners remain separate: raw execution halts on errors; surface execution
can continue with the connection produced from an error. Combining these into a
general interpreter would add scope without evidence of a present benefit.

## Required implementation guarantees

- Preserve the exact quantified old formulas, with generic applications as their
  proofs. Do not retain old public aliases. At minimum, check both raw formulas
  and both surface formulas from the experiment as acceptance examples.
- Keep the original effect contract: success and partial constraint failure
  constrain the effect database; other failures rely on existing state/outcome
  transport. Preserve pending persisted and visible databases and all saved
  transaction databases through the existing carriers.
- Preserve arbitrary positions, clocks, counters, parameters, states, scripts,
  connections, and resolver contexts in the quantified proofs. The ordinary
  run uses the default absent two-state `initial` database. Extending query
  observation APIs to a nondefault `initial` is outside this experiment.
- Keep the state support check stronger than raw readiness. It also checks that
  read counters are known. The tested implication goes from state readiness to
  raw readiness; replacing it by an equivalence is invalid.
- Require no suffix conditions after a raw halt or a surface ended step. The
  halting step still has its own obligation. `ContextLaws` checks these formulas.
- Preserve separate atom access and conjunction of certificates. `keeps_and`
  checks conjunction without adding any readiness requirement.
- Delete the parallel ready/unconditional run and surface step APIs after
  callers move. Keep effect-carrier lemmas and semantic atom conditions. Do not
  infer further deletion from the experiment's imports.

## Evidence limits

These experiments prove expressibility and theorem-strength preservation, not
the net source reduction after migrating every caller or any build-speed gain.
The old APIs are imported to state exact formulas and use existing low-level
transport lemmas. The production migration must remove the replaced APIs and
their dependencies rather than importing them under the new implementation.

All experiment files enable checked Verso docstrings. Each decisive theorem has
an explicit axiom audit. Local diagnostics report only `propext`,
`Classical.choice`, and `Quot.sound`; the Nix acceptance check is authoritative.
