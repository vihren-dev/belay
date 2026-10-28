# ADR 0026: Shared semantic facts for query and execution proofs

Date: 2026-10-26. Status: ACCEPTED for implementation by the owner on 2026-10-28.
Audience: designers and reviewers.
Owner request: test the causes of proof duplication, then specify the refactor
supported by the results.
Evidence: [experiment record](../experiments/proof-boundaries/README.md).
Direction: [Lean simplification goal](lean-simplification-goal.md); related [ADR 0025](adr-0025-compositional-preservation-proofs.md).

## Problem

Several proof families start from a specialized observation and repeat the
reasoning that produces it. Query families expose rows, emptiness and errors
separately. Current- and initial-database independence each traverse sources and
nested queries. Three resolver proofs each dispatch over statement syntax.
Expression equality proofs each traverse expressions. Four execution relations
repeat equality and branch-matching arguments.

The common facts are sometimes in files owned by their specializations. This
import direction prevents those specializations from sharing a lower proof
without moving definitions. Broad imports also load unrelated proof families.
The dependency report identifies candidates; compiled prototypes establish
which candidates actually share reasoning.

## D1. Describe query execution before applying an observer

Each query family has a semantic characterization that retains the complete
modeled output. Row, emptiness, error and other predicates follow by rewriting
that characterization. Keep resolution facts separate when their assumptions
are weaker than execution facts. Use ordinary equality and simplification for
predicate transport; no new observer framework is required.

Replace 45 endpoints in the current seven-family inventory: 21 model and 24
surface endpoints. The three added filtered duplicate-key observations share
the generalized grouping family; retain its filter, grouped-column and resolution
premises. Keep filtered/unfiltered pairwise and unique-lookup results. Historical
prototypes check count, aggregate and one surface count application; the other
five families and new filtered cases remain implementation obligations. Reuse
the existing simple-table `_agree`/`_append` output laws and their distinct premises.

The complete output retains possible results, unmodeled cases, error codes and
error precedence. A no-error result cannot acquire a clean-source or
window-binding premise merely because a row characterization needs one.

## D2. Share source traversal through observed database agreement

One source-agreement argument owns joins, source folds and subquery depth.
Current table sources compare their current table lookup; initial table sources
compare their optional initial table lookup; pragmas compare their actual rows
result. JSON and derived sources need no further database premise when their
evaluation context and intermediate rows agree.

Lookup equality retains absence and full table shape. It is a sufficient
contract, not a claim about the minimum fields each query reads. The existing
current/initial irrelevance claims follow through small origin adapters with
their original premises. Replace the fourteen mirrored helper stages rather
than leaving a second traversal behind the new API.

## D3. Certify a resolved statement once

One statement-syntax dispatch proves a result certificate. State equality is
unconditional after successful resolution. Schema linkage is conditional on
the input catalog's validity at arbitrary supplied limits. Next-state validity
is conditional on execution mode and the full input state's validity at the
context's limits. These conditions belong to separate certificate fields.

Catalog/write transport facts combine the existing leaf resolver facts. Current
and saved transaction catalogs retain their distinct behavior. The applied
catalog validity consumer retains its formula for control statements too;
control statements leave the applied catalog unchanged. No stronger common
premise may be imposed merely to bundle the facts. Include RENAME and INSERT
SELECT and DROP COLUMN, reusing `RenameOutcome`, `DropOutcome` and traced-resolver
equations. Preserve traces and the executable/proof import split: script
resolution imports `ResolveStatement`; proof consumers import `StatementArms`.

## D4. Use equality of observation profiles

An execution profile consists of its actual observation and a predicate of all
possible observations. Ordinary equality gives the relation laws. One branch
transport law and one singleton law serve the existing relations.

The observer distinguishes full execution, value/trace observation, full views
and weak views. Keep complete connection state and raw step counts wherever
the original relation observes them. Actual output is retained separately from
possible outputs. Branches first select an execution and its next connection,
then an output choice; singleton proofs must exclude further executions too.
Strengthening weak observation requires its existing frame
premises. Sequential composition retains its existing continuation obligations.
Full-state simulation and interface-scoped simulation remain distinct.
Preserve the new NOT IN/EXISTS equivalences as consumers, with their distinct
NULL, rowid-alias, affinity and resolution premises.
Retain read-certificate transport between named tables at different positions
and across every migration branch, including branches with different end states.

## D5. Generalize expression congruence, retain separate fault guarantees

One mutual induction preserves the evaluation value, fault and JSON subtype
when the primitive observations used by the expression agree. Scalar,
membership and existence subqueries keep their different observed values and
certainty rules. Lazy scalar calls retain the operand results they inspect.

Derive append, subquery-context replacement, certain-first context replacement
and rowwise congruence from this argument. The two context-replacement claims
can omit their old no-fallible-call premises, as the experiment proves. Other
caller conditions and SQL admission rules change only if separately justified.
Keep rowwise fault-freedom and calmness distinct from read locality. A local
JSON call can fail. Retain `Expr.evaluate_dropColumn` as a distinct transformation
proof: its two expressions differ, beyond the tested fixed-expression congruence.

## D6. Put shared primitives below their consumers

This is the bounded import cleanup requested in the owner's investigation of
codebase modularity and the dependency report. The demonstrated moves define
its scope; an unmeasured performance benefit is not its justification.

Move the three remaining primitive facts to suitable foundational owners.
Reuse `LiteralData.generatedCells_plain`, already moved to `AdmittedCellLaws`,
and the general derived-column laws that replaced `NormalizedField*`.
Put shared definitions below specialized laws.
Remove the model umbrella imports from the three demonstrated surface modules:
`Values`, `Script` and `ValueDisplay`. Their complete unchanged bodies compile
with narrower imports at the experiment baseline. Public aggregation remains available.

Historical import closures decreased from 580 to 75, 142 and 148 in those
probes. Recheck current imports; those counts establish no current timing gain.
Any further import changes require source-use checks and compilation, including
instances, syntax, simp registrations, exports and checked documentation.

## D7. Defer a shared row-engine interface

Both tested abstractions compile, but the interface and instance obligations
outweigh the shared traversal in the measured source. The broad prototype adds
another description of generated work. The narrow version still adds witnesses
around already compact callers. Keep the current specialized trigger proofs.
This ADR creates no row-engine implementation work.

The FK stop predicate, permitted work and physical phase boundaries remain real
distinctions. A future proposal must simplify actual callers and count the
interface, witnesses and remaining specializations together.

## Compatibility, evidence and scope

Test lifetime amended 2026-10-26 with owner approval.
Source scope reconciled 2026-10-28 with `main` at `3e2212ed`; accepted prototypes
remain evidence for `3fe5caef`, not a compile result for the rebased branch.

These decisions change proof interfaces, not SQL execution or supported SQL.
The project has no users: migrate callers and delete replaced declarations and
aliases. Preserve their mathematical guarantees through complete migration
checks, then retain focused coverage of current contracts. A zero-consumer
graph node alone does not justify deletion of useful semantic or simp facts.

Old-formula matrices, old/new representation adapters, duplicate primitive
proofs and baseline/narrow import copies are temporary acceptance witnesses.
Keep one copy through the last planned slice that changes their contracts.
Record Nix acceptance against that final implementation, then delete redundant
temporary test sources and registrations before completing the refactor.
Historical experiments remain replayable at their recorded revision, outside
normal CI; this includes the deferred row-engine prototypes.

Retain a case if it uniquely protects a premise boundary, semantic distinction
or trust guarantee until a migrated consumer or focused regression covers it.
Use existing public examples, checked documentation and conformance first.
Audit generic proofs and independently proved instances with existing tools;
remove duplicate audits of trivial projections. Tests of ordinary equality
laws or substitution alone add no repository-specific guarantee.

Old-endpoint dependency inspections, frozen inventories and before/after import
or source-size measurements are one-time acceptance work, not CI snapshots.
Record acceptance and retirement in existing status files. No new manifest,
runner or permanent ADR-specific suite is required.

ADR 0025 still owns invariant preservation and contextual script conditions.
ADR 0025 explicitly leaves query observation transport, resolver provenance,
subquery traversal and import-barrel policy outside its scope. This ADR adds
the report-driven source-agreement, expression-congruence and execution-profile
work and the demonstrated import cleanup. It supersedes
named-endpoint obligations and ongoing retired-endpoint test matrices for the
replaced families; their mathematical guarantees remain obligations.
No package split, evaluator rewrite, proof registry or performance target is
introduced. Production source reduction and proof/build costs are measured
after migration; the experiment makes no net-saving or speed claim.

## Implementation specifications

- [Query outputs and execution observations](spec-proof-observations.md), with
  [endpoint, relation and caller targets](spec-proof-query-observation-targets.md).
- [Source and expression agreement](spec-proof-agreement.md), with
  [traversal, congruence and definition targets](spec-proof-agreement-targets.md).
- [Resolver certificates and primitive ownership](spec-proof-foundations.md), with
  [dispatch, relocation, import and deferred targets](spec-proof-resolver-foundation-targets.md).

The grouped target inventories were added 2026-10-27 at the owner's request
and rechecked 2026-10-28 against production revision `3e2212ed`. They separate required
changes, placement choices, reused evidence and retained or deferred work.
Reconcile branch drift at assignment and update links when owner files disappear.
They do not introduce permanent inventory checks or alter test retirement.

Assigned: [primitive ownership and surface imports](../plans/20261028-proof-primitive-imports.task.md)
and [shared source agreement](../plans/20261028-source-agreement.task.md),
plus [expression congruence](../plans/20261028-expression-congruence.task.md)
and [execution observation profiles](../plans/20261028-execution-profiles.task.md).
Create further tasks only at assignment; batch edits by decision.
