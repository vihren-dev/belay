# Unify preservation runs with execution-aware conditions

Date: 2026-10-26. Status: READY; implementation has not started.
Audience: the implementation team.
Specification: [ADR 0025 D3 and D4](../docs/adr-0025-compositional-preservation-proofs.md).
Record: [status](20261026-preservation-context.status.md).
Targets: [condition, induction and evidence inventory](../docs/spec-preservation-proof-targets.md).
Baseline reviewed 2026-10-28: production revision `3e2212ed6983`.
Present problem: conditions omit the clock, counters and parameters, causing
parallel readiness-dependent step/run proofs and a repeated surface traversal.

## Required behavior

One statement-preservation contract can express conditions on the five inputs
passed by ordinary script execution to `runStatement`: clock, visible counters, parameter list,
resolved statement and database. Conditions that ignore inputs remain easy to
write. Readiness is a condition for proofs that require it, not a universal
precondition on every preservation theorem.
The conclusion covers every member of `StatementRun.effects`, including
alternative INSERT-query effects. It cannot be weakened to the canonical effect.
These runners use the default `initial := none`; two-state observation APIs
that supply an initial database are outside this preservation task.

One resolved-script preservation induction handles ordinary and support-dependent
invariants. Its conditions follow actual reached states and stop at a halted
transition. The existing unconditional and ready generic formulas remain
derivable with exactly their original assumptions. The `runSql` entry laws specialize
the same induction and retain all current guarantees.

One surface-script preservation induction covers every complete execution, and
one continuing-step proof covers every `RunStep.executions` member. Both explicit
reached-step obligations and resolver-derived obligations use those proofs.
The derived form uses the invariant at each branch's reached connection;
conditions inspect that branch's actual database and counters. Canonical-run
guarantees follow from membership in the complete executions, without another
preservation induction.
Unresolved statements and suffixes after an ended run impose no obligations.
The actual selected clock and visible counters are used; mode and limits stay
explicit where resolution requires them.

Update all preservation evidence, conjunction composition, resolver bridges,
callers and documentation to the unified interface. Delete the parallel
production contracts and traversals. Old-formula adapters are temporary
migration witnesses under ADR 0025 D4, not permanent compatibility APIs or tests.
Preserve the own-run-to-all-effects bridge with an explicit implication from
the INSERT-query condition to the corresponding upsert condition at the same
clock, visible counters, parameters and database. Readiness-dependent instances
use the existing readiness implication; input dependence does not imply it away.

## Acceptance checks

- Kernel-check both old generic resolved-run formulas through the new
  induction, for arbitrary property, condition, position, script and state.
  An unconditional formula must compile without `supportedSqlFrom` or a raw
  readiness premise. A ready formula retains its existing supported-run premise.
- Kernel-check the current all-execution and canonical generic surface formulas,
  for explicit and invariant/resolver-derived conditions. Include a genuinely
  input-dependent condition so ignoring parameters, counters or the selected
  clock cannot satisfy the check accidentally. Check a branch-divergent INSERT
  from a query and later obligations on each branch. Reuse existing
  `InsertSelectExecutions` cases where they provide this coverage.
- Verify reached-state behavior, a nonzero start position, open transactions,
  rollback snapshots, partial FAIL and pending outcomes. A halted suffix has
  no condition even when its hypothetical condition is false. Retain existing
  necessity examples and add only missing focused checks.
- The state support check implies raw statement readiness, while its counter
  knowledge requirement remains additional. Test an example where this
  distinction matters. The two checks must not be treated as equivalent.
- Re-establish the affected `3e2212ed6983` per-atom migration formulas against the final
  condition contracts, sharing temporary witnesses with the API task. Compile
  existing statement/script preservation examples. Audit new generic proofs
  and independently proved invariant evidence under the standard axiom policy.
  The full model and surface packages, checked docs and existing Nix acceptance
  suites pass.
  Preserve the current FK rename selection premise and the unconditional
  DROP COLUMN cases; the older rename guard is no longer their contract.
- Confirm there is one production preservation induction for each executor
  and no retained old-interface traversal. Report net proof changes and any
  material elaboration-cost changes; source reduction alone proves no speedup.

Use the repository's current Nix suite owners and check cadence. Commands have
configured timeouts. No new general execution framework or CI service is part
of this work.

## Test lifetime

After the final affected contract change passes Nix acceptance, remove redundant
old-condition adapters and per-atom formula matrices from active test sources
and registrations. Preserve their historical acceptance record. Keep focused
checks for unconditional versus supported premises, input-dependent conditions,
guarantees for all effects and branches, reached states, halt boundaries,
transaction/FAIL outcomes and counter knowledge.
Reuse existing clients and necessity examples before adding a case. These checks
protect different semantics; they need not repeat every invariant at every run
entry point. Record retirement in the existing status file.

## Relevant code and traps

`RunHolds`, `RunHoldsReady`, `ScriptConditions`, `ScriptRunHolds`, `ScriptRunDerived`,
`RunHoldsStep`, `SqlAdvance` and `StatementStep` contain the affected contracts
and transport. `advanceWith_holds`, `SqlTransition.counted_holds`,
`Connection.afterStep_holds` and `SqlState.finish_holds` already handle retained
databases and can remain the transport foundation.
`InsertSelectKeeps` owns `StatementKeeps.ofOwnRun` and
`StatementKeepsReady.ofOwnRun`; migrate their compatibility premises with the
condition interface. `ScriptRunAll` supplies canonical-run membership.
`ScriptRunSingleton` also consumes `ScriptConditionsWith` and must migrate.
The separate relations in `ExecutionCounters` retain their meanings.

Raw `runSqlFrom` does not apply the surface support gate. `SqlState.statementRun`
uses `state.counters.view statement.counterReads`, and its ready flag includes
counter knowledge. Surface execution obtains its clock from `statementClock`.
Do not substitute zero, the input connection's clock function, or the full
counter record for the actual evaluator inputs.

The historical experiment's conversions predate all-effects/all-execution
contracts and are not current compatibility evidence. Production callers use
the new conditions directly, so those conversions do not become another family
of duplicated run proofs.
Coordinate this task with the API-removal task's final names. Statement engine,
resolver, output semantics and conformance expectations remain unchanged.
