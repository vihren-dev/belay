# Unify preservation runs with execution-aware conditions

Date: 2026-10-26. Status: READY; implementation has not started.
Audience: the implementation team.
Specification: [ADR 0025 D3 and D4](../docs/adr-0025-compositional-preservation-proofs.md).
Record: [status](20261026-preservation-context.status.md).
Present problem: conditions omit the clock, counters and parameters, causing
parallel readiness-dependent step/run proofs and a repeated surface traversal.

## Required behavior

One statement-preservation contract can express conditions on the five inputs
passed by ordinary script execution to `runStatement`: clock, visible counters, parameter list,
resolved statement and database. Conditions that ignore inputs remain easy to
write. Readiness is a condition for proofs that require it, not a universal
precondition on every preservation theorem.
These runners use the default `initial := none`; two-state observation APIs
that supply an initial database are outside this preservation task.

One resolved-script preservation induction handles ordinary and support-dependent
invariants. Its conditions follow actual reached states and stop at a halted
transition. The existing unconditional and ready generic formulas remain
derivable with exactly their original assumptions. The `runSql` entry laws specialize
the same induction and retain all current guarantees.

One surface-script preservation induction and one continuing-step proof serve
both explicit reached-step obligations and resolver-derived obligations.
The derived form uses the current invariant at each reached connection.
Unresolved statements and suffixes after an ended run impose no obligations.
The actual selected clock and visible counters are used; mode and limits stay
explicit where resolution requires them.

Update all preservation evidence, conjunction composition, resolver bridges,
callers and documentation to the unified interface. Delete the parallel
production contracts and traversals. Old-formula adapters may exist as
experiment/test proofs; they are not compatibility APIs in production.

## Acceptance checks

- Kernel-check both old generic resolved-run formulas through the new
  induction, for arbitrary property, condition, position, script and state.
  An unconditional formula must compile without `supportedSqlFrom` or a raw
  readiness premise. A ready formula retains its existing supported-run premise.
- Kernel-check both old generic surface-run formulas: explicit script
  conditions and invariant/resolver-derived conditions. Include a genuinely
  input-dependent condition so ignoring parameters, counters or the selected
  clock cannot satisfy the check accidentally.
- Verify reached-state behavior, a nonzero start position, open transactions,
  rollback snapshots, partial FAIL and pending outcomes. A halted suffix has
  no condition even when its hypothetical condition is false. Retain existing
  necessity examples and add only missing focused checks.
- The state support check implies raw statement readiness, while its counter
  knowledge requirement remains additional. Test an example where this
  distinction matters. The two checks must not be treated as equivalent.
- Re-run all migrated per-atom formula checks and existing statement/script
  preservation examples. Audit the new generic proofs and representative
  clients for the standard axiom policy. The full model and surface packages,
  checked docs and existing Nix acceptance suites pass.
- Confirm there is one production preservation induction for each executor
  and no retained old-interface traversal. Report net proof changes and any
  material elaboration-cost changes; source reduction alone proves no speedup.

Use the repository's current Nix suite owners and check cadence. Commands have
configured timeouts. No new general execution framework or CI service is part
of this work.

## Relevant code and traps

`RunHolds`, `RunHoldsReady`, `ScriptRunHolds`, `ScriptRunDerived`,
`RunHoldsStep`, `SqlAdvance` and `StatementStep` contain the affected contracts
and transport. `advanceWith_holds`, `SqlTransition.counted_holds`,
`Connection.afterStep_holds` and `SqlState.finish_holds` already handle retained
databases and can remain the transport foundation.

Raw `runSqlFrom` does not apply the surface support gate. `SqlState.statementRun`
uses `state.counters.view statement.counterReads`, and its ready flag includes
counter knowledge. Surface execution obtains its clock from `statementClock`.
Do not substitute zero, the input connection's clock function, or the full
counter record for the actual evaluator inputs.

The experiment's old-condition conversion lemmas exist to prove formula
compatibility. Production callers should use the new conditions directly,
so those conversions do not become another family of duplicated run proofs.
Coordinate this task with the API-removal task's final names. Statement engine,
resolver, output semantics and conformance expectations remain unchanged.
