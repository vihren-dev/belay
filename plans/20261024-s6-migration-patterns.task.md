# S6: migration observation views and comparison patterns

Created 2026-10-24. Status: OPEN. Implementation follows reviewed execution
contracts. Status: [progress](20261024-s6-migration-patterns.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S6; accepted observation-view
and full-context decisions; [execution contracts](20261024-s6-execution-contracts.task.md).

## Purpose and boundary

Users can state query preservation, query translation and migration commutation
without treating a migration's ordinary outputs as application observations.
The view names which execution segment supplies those outputs. It never changes
execution. Ordinary strong equivalence retains all outputs and all context.

The production execution task supplies branch outcomes and strong/weak relations.
This task adds views, named patterns, their laws and corrected migration examples.
The S6 assertion task supplies fresh triples and before observations separately.
S8 supplies interfaces and whole-application simulation. Automation consumes
these proved contracts in a later task; a general footprint framework is not a
prerequisite for defining these comparisons.

## Required outcomes

- **A view identifies actual execution segments.** Expose a small public
  descriptor/witness for the migration segment and its surrounding computation.
  Interpretation executes the original Sql program with the same values,
  outputs, SQL errors, unmodeled termination, clock/index and full connection.
  Segment identity follows actual bind/branch execution, including a migration
  chosen using an earlier result. Do not infer boundaries by searching output
  values, deleting equal rows or assuming every script reaches its last step.
  An explicit witness remains available when convenient syntax is ambiguous.
- **Projection changes only the specified observation.** The migration view
  leaves the segment's successful outputs out of the compared trace. It retains
  failures, unmodeled reasons, partial termination and the real reached state.
  The program's returned value is unchanged, including a value that contains
  migration outputs. Users choose a program returning only the application
  value when that is the intended comparison. Counter changes and statement
  clock advancement remain observable to later SQL. Quiet is a view descriptor,
  not a Sql action that erases outputs from ordinary execution/equivalence.
- **Views cover every branch.** Project the actual run and each permitted raw
  and concrete branch outcome from the execution contract. Keep stopped outcomes
  and the trace produced before stopping. Prove interpretation erasure, identity
  view, segment concatenation and appropriate composition laws. Result-dependent
  bind needs a view of its actual continuation; a proof cannot supply a mask for
  only the canonical result. Keep the primitive explicit when a convenience
  rule cannot prove the needed correspondence of segments.
- **Weak and full comparisons remain distinct.** Provide the named comparison
  of projected values/traces with final state omitted. Provide the full-context
  comparison of projected values/traces plus complete final connection, clock
  and next index. The output trace is compared through the view; every non-trace
  context component is compared exactly. Both retain actual-run agreement and
  all-branch outcome agreement. Prove identity-view bridges to the corresponding
  execution relations. A projected comparison never silently becomes ordinary
  strong equivalence or an unrestricted bind congruence.
- **Migration domains are explicit and noncircular.** A fixed-context primitive
  states its admissible context predicate and migration-success assumption.
  Success uses modeled, error-free execution on the actual and every permitted
  branch. The convenient pattern's domain tests the migration at the original
  context. It must not exclude an application write merely because moving that
  write before the migration makes the later migration fail. Such a failure is
  an observable failed comparison. Define any stronger domain as a separate
  explicit restriction. No comparison proposition is its own domain premise.
- **Preservation and translation compare query observations.** Define the
  meaning of M preserves Q and M translates Q to Q2 over the declared migration
  domain. Compare Q at the original context with Q2 after M, with only M's
  segment projected out. Keep query outputs, return values, errors and all
  permitted alternatives. The general primitive supports arbitrary supplied
  contexts; convenience forms quantify over every complete fresh environment
  and admitted database. State query/read-only admission conditions at the
  surface. Preserve a flexible primitive for comparisons outside that helper.
- **Commutation compares the full reached context.** Define S commutes with M
  as the special case of S commutes with M as S2. Compare S followed by M with
  M followed by S2 using corresponding migration segments and retaining the
  application return values. Complete final connection, clock and next index
  must agree, even when final rows and visible outputs agree. Queries can use
  this stronger condition too. Supply named unrestricted/contextual/restricted
  laws with exact domain-preservation premises rather than hidden fresh resets.
- **Pattern laws are proved from execution.** Supply reflexive/identity and
  composition laws that hold for the stated domains, plus usable sufficient
  bridges from query translation to full contextual commutation. Those bridges
  name the required frame, counter, clock and resolution conditions. Read-only
  syntax alone is insufficient. A migration succeeds claim is separate from a
  pattern: an empty success domain can make a pattern vacuous, which its docs
  and explanation must state. Expose all definitions and laws without notation.
- **Guide migration examples state the true comparison.** Prove the normalized
  field expansion's read-query preservation/translation under explicit schema,
  effect and environment conditions. Preserve universal quantification over
  admitted databases and parameters. Its write/expansion orders can produce
  total_changes 3 versus 4; retain a checked full-context counterexample and
  direct the positive application claim to S8's explicit scoped relation.
  Do not present that write pair as full commutation. The weaker query theorem
  remains useful even when full commutation is false.
- **The rebuild example detects data loss.** With the separately completed
  table-rebuild and FK semantics, check the cascade failure when DROP TABLE
  follows the copy, including the ignored pragma inside a transaction. Prove
  the corrected migration preserves the required query under explicit schema,
  binding, success and effect conditions, with foreign keys enabled before the
  transaction in enforcement examples. Retain the type-affinity data-loss
  example. Existing default FK and DQS settings remain unchanged.
- **Notation, explanation and guide agree.** Pattern syntax, where guards and
  any quiet convenience elaborate to the explicit view/domain primitives.
  Default SQL guards retain default Holds observation, with explicit context
  predicates available for stronger conditions. Explain the compared segments,
  domain, errors, state scope and vacuity. Update all private guide formulas,
  tables and complete-example occurrences; private prose stays private.

## Tests and acceptance

Installed-library kernel fixtures compare a descriptor's interpretation with
the original program. Exercise empty and multi-statement segments, duplicate
outputs across segments, result-dependent branches, raw and concrete oneOf,
errors followed by writes and unmodeled stops inside/outside the migration.
Assert exact values, traces, counters, snapshots and advanced clock indices.
Check that projected migration outputs still occur in ordinary Sql.run.

Positive/negative fixtures distinguish weak projection, full-context projection
and ordinary strong equivalence. A clock-storing migration after a constant-row
query refutes lifting from weak query translation. A successful original
migration that fails after a preceding write must fail the corresponding
commutation check, not vanish from its domain. Include a failed migration
outside the convenient domain and state the resulting vacuity explicitly.

Prove the universal query preservation/translation examples and corrected
rebuild theorem with only accepted Lean logical axioms. Check concrete native
counter, cascade, affinity and trigger examples against model execution. Audit
all theorem dependencies for sorryAx, ofReduceBool, _native and assumed semantic
soundness. Frontend tests check actual explanations and source diagnostics.

Two acceptance parts: public views, comparisons, pattern meanings and laws;
universal migration examples, diagnostics and private guide integration. Each
coherent commit gets focused checks, dev-build and independent review. Each
part ends with post-review just test-full and just verdict; task end runs
just test-nix and just test-scheduled-checks under the build-boundary override.
All subprocess tests have finite timeouts. Only Nix results are acceptance
evidence. New corpus/claim changes use a separate judge PR; no locked claim is
changed in the implementation PR.

## Inputs and ownership

Production branch/WP/equivalence modules do not exist in this planning tree;
their reviewed task is linked above. Prototype findings are at c838d5cc in
sqlite-verifier-s6-foundations, with completed acceptance at eb0a16a9. They are
design inputs, not production dependencies. Final S4 supplies run and success
laws. The table-rebuild task and foreign-key-atoms task own their model changes;
their final reviewed revisions are required for rebuild acceptance.

Reserve surface exports, test manifests and the private guide before editing.
Keep execution descriptors, projections, relational laws and surface notation
in separate modules below 200 lines, with checked plain-words documentation.
Do not duplicate execution, introduce writable attachments or change strong
equivalence. Report a demonstrated contract contradiction before changing its
meaning; continue independent work while a decision is pending.
