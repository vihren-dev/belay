# ADR 0026: Shared semantic facts for query and execution proofs

Date: 2026-10-26. Status: PROPOSED; experiment-checked.
Audience: designers and reviewers.
Owner request: test the causes of proof duplication, then specify the refactor
supported by the results.
Evidence: [experiment record](../experiments/proof-boundaries/README.md).
Related: [ADR 0025](adr-0025-compositional-preservation-proofs.md).

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

Replace the 42 model/surface observation endpoints in the seven-family
experiment inventory. Their original formulas remain derivable under their
original assumptions. This is an initial replacement scope, not a claim that
42 independent mathematical facts disappear. Keep useful pairwise duplicate-key
and unique-lookup results. Count, aggregate and one surface count application
have been prototyped; migration of the other five families remains required.

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
premise may be imposed merely to bundle the facts.

## D4. Use equality of observation profiles

An execution profile consists of its actual observation and a predicate of all
possible observations. Ordinary equality gives the relation laws. One branch
transport law and one singleton law serve the existing relations.

The observer distinguishes full execution, value/trace observation, full views
and weak views. Keep complete connection state and raw step counts wherever
the original relation observes them. Actual output is retained separately from
possible outputs. Strengthening weak observation requires its existing frame
premises. Sequential composition retains its existing continuation obligations.
Full-state simulation and interface-scoped simulation remain distinct.

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
JSON call can fail. This decision covers congruence, not all expression proofs.

## D6. Put shared primitives below their consumers

This is the bounded import cleanup requested in the owner's investigation of
codebase modularity and the dependency report. The demonstrated moves define
its scope; an unmeasured performance benefit is not its justification.

Move the four demonstrated primitive facts to suitable foundational owners.
Place definitions used by shared proofs below the specialized laws they replace.
Remove the model umbrella imports from the three demonstrated surface modules:
`Values`, `Script` and `ValueDisplay`. Their complete unchanged bodies compile
with narrower imports in the experiment. Public aggregation remains available.

Project import closures decrease from 580 modules to 75, 142 and 148 in those
three probes. These counts establish narrower dependencies, not faster builds.
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
and checked against production revision `3fe5caef`. They separate required
changes, placement choices, reused evidence and retained or deferred work.
Reconcile branch drift at assignment and update links when owner files disappear.
They do not introduce permanent inventory checks or alter test retirement.

These specify outcomes and checks. Create dated implementation task/status files
only when an implementer is about to take the work. Batch their edits by decision.
