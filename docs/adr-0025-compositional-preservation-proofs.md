# ADR 0025: A compositional preservation proof API

Date: 2026-10-26. Status: PROPOSED; experiment-checked and ready for implementation review.
Audience: designers and reviewers.
Owner request: simplify the theorem and proof API, including changing the
per-atom product contracts, after experiments in a separate workspace.
Related: [ADR 0022](adr-0022-database-validity.md),
[ADR 0013](adr-0013-model-structure.md), and
[ADR 0016](adr-0016-model-and-surface.md).
Evidence: [experiment record](../experiments/proof-simplification/README.md).

## Problem

The preservation layer repeats facts at several levels. Each invariant has
statement evidence, named theorems for several run entry points, specialized
condition names, and tests for those names. Some statement families also repeat
the complete dispatch over statement constructors. The general proof machinery
exists, but some general lemmas import earlier specializations. Reusing them
from those specializations would create import cycles.

`StatementKeeps` quantifies over the clock, counters and parameters, while its
condition can mention only the statement and database. `StatementKeepsReady`
and a second run traversal compensate for that restriction. Surface execution
then repeats the step analysis and run traversal for derived conditions.

These are current maintenance problems identified in the owner's review, not
requirements for a speculative framework. Experiments use integration commit
`6413afe3ff50`; concurrent name-trace work is outside that frozen baseline.

## D1. Guarantees are derivable through generic laws

Each invariant retains its definition, decidable checks, equivalence proofs,
and preservation evidence with its actual conditions. A caller combines that
evidence with a generic execution law. A separate public theorem for every
invariant and entry point is no longer required.

The initial deletion scope is the 84 wrappers in the experiment inventory:
54 run specializations and 30 statement specializations. Their declaration and
docstring spans total 937 lines. Six pure-wrapper modules total 664 full-file
lines; those lines overlap the declaration count. These are gross removal
opportunities, not measured net source or compilation savings.

Use existing `Effect.Satisfies`, `SqlState.Holds`, `Outcome.Holds`, generic run
laws and preservation evidence. Remove specialized aliases when their only
purpose is to restate a generic application. Small bundled helpers with concrete
callers can remain: `runScriptFrom_valid` and `runScriptStep_valid` serve the
surface program API. `runScriptFrom_admittedWith` is generic and remains useful.
The inventory is the required initial removal set, not a mandate to delete
semantically distinct statements that happen to have similar names.

The project has no users. Update callers and delete replaced names, exports,
Lake roots and paths. There are no compatibility aliases. Retain historical
records and experiment inputs needed to replay the evidence.

## D2. General preservation facts own the foundations

The lowest proof layer contains the existing effect/state predicates and
database update facts needed by multiple invariant families. Table-level
preservation uses the weakest existing contract, `TableAtom` (empty tables and
sublists). Row-local constraint facts supply that contract plus their constraint
implication. They do not own a second implementation of the same frame facts.

One general table-atom statement theorem owns the complete dispatch for the
families it covers. Row-local atoms and distinct rowids supply their ADD COLUMN,
plain-write and row-engine facts. Their existing formulas remain derivable
without readiness or extra admitted-database premises.

General `setRows`, checked-write and insert-outcome lemmas sit below their
instances. Imports must allow the instances to use these lemmas without cycles
or importing unrelated atom instances merely to get a general primitive.
This is a relocation and consolidation of existing machinery. It introduces
neither a universal schema-invariant interface nor a new proof registry.

Catalog-selected unique keys and cross-table foreign keys remain distinct where
their dependencies require it. A catalog-aware `setRows` fact can serve unique
keys without forcing their whole statement theorem into `TableAtom`.

## D3. Conditions can inspect actual execution inputs

The generic statement-preservation condition can depend on the clock value,
visible counters, parameters, resolved statement and database passed to
`runStatement` by ordinary script execution, with its optional `initial`
database left at `none`. Two-state observation APIs remain outside this scope.
Ordinary conditions ignore the additional arguments. Readiness
is an explicit condition for invariants that need it.

There is one preservation induction for resolved scripts. Its conditions follow
the reached execution states and require nothing of a suffix after a halt.
An unconditional invariant still has a run guarantee without a support premise.
A readiness-dependent invariant can recover its current guarantee from
`supportedSqlFrom` and the other original conditions.

There is one preservation induction for surface scripts, with a shared proof of
the continuing step. It admits explicit reached-step conditions and conditions
derived from resolution and the current invariant. Execution mode and matching
limits remain premises where the resolver needs them. The surface uses the
clock selected by `statementClock`; it does not substitute the raw runner's
clock assignment. The state readiness check includes counter knowledge in
addition to raw `runStatement` readiness. That implication is used in its
proved direction only.

These changes affect proof interfaces. They do not change executable stepping,
the support gate, evaluation, errors, observations or the modeled SQL subset.

## D4. Formula strength and trust remain acceptance criteria

Test lifetime amended 2026-10-26 with owner approval.

The replacement must derive each removed endpoint's old mathematical claim
with the same entry assumptions. Exhaustive old-formula checks are temporary
migration evidence. Keep one copy through the last planned slice that changes
their shared contracts, and record Nix acceptance against the final migrated
implementation. Then delete redundant temporary test sources and registrations
before completing the refactor. Historical witnesses remain replayable at their
recorded revision; they need not compile against later APIs.

Permanent coverage protects generic contracts, independently different premise
requirements, semantic distinctions and real clients. Retain any migration case
that uniquely checks such a requirement until a current consumer or focused
regression covers it. In particular, ordinary compilation does not detect an
accidentally stronger hypothesis or a weaker definition. Reuse existing native
necessity examples, checked documentation and conformance. Audit generic proofs
and independently proved invariant evidence under the existing axiom policy;
trivial wrapper projections do not need duplicate audits.

Frozen inventories, old-name dependency inspections, import comparisons and
source-size reports are one-time acceptance work. Record acceptance and test
retirement in the existing status files. There is no new test manifest, runner
or permanent suite for this migration, and no lasting invariant-by-executor
matrix solely to preserve the removed API's layout.

Preservation covers the current database and saved transaction snapshot, the
database carried by partial constraint FAIL, and the appropriate databases of
success, failure and pending outcomes. Other effect errors require no property
of their discarded database; the run proof handles the retained input or
rollback snapshot. Suffixes after a raw halt or surface ended step impose no
conditions. A surface step with failed resolution, clock selection or support
imposes no contextual step condition. The raw halting step retains its own
condition; only its suffix is vacuous.

Independent atoms remain usable independently. `RowsStoredWide` and
`RowsAliasedSupported` retain their real width and catalog dependencies.
The FK schema and row-reference atoms, explicit versus selected mappings, and
the comparison/work conditions remain distinct. The refactor cannot assume
that enabled FK enforcement preserves every schema fact.

All accepted proof closures use only the standard axioms already allowed by
the model tests: `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`,
native evaluator axiom, new axiom or trusted shortcut is introduced.

## Scope and supersession

On adoption, D1 supersedes the requirement for separately named per-atom run
and statement endpoints in ADR 0022 D3 and in the completed keys-unique,
Valid-atoms and Admitted-atoms tasks. It also replaces named run specializations
in the foreign-key task. D4 also supersedes ongoing name/formula-matrix checks
for retired endpoints in those tasks. Their mathematical claims, distinct
premise requirements, necessity examples and axiom policy remain obligations.
Historical task/status records continue to describe their original delivery;
they are not rewritten as if this refactor already existed.

Resolver provenance contracts, query observation transport, subquery traversal
invariants, package splitting, import-barrel policy and foreign-key engine
recursion are separate opportunities. This ADR does not authorize those changes.

## Implementation specifications

| Task | Result | Dependency |
| --- | --- | --- |
| [Proof API](../plans/20261026-preservation-api.task.md) | Generic applications replace the endpoint matrix | Foundations provide cycle-safe generic effect predicates |
| [Proof foundations](../plans/20261026-preservation-foundations.task.md) | General primitives and one table-atom dispatch | Existing integration baseline |
| [Execution conditions](../plans/20261026-preservation-context.task.md) | One run induction per executor | API removal establishes the names and temporary migration witnesses |

The tasks specify separate reviewable results, not a prescribed coding order.
Their implementation is not part of the experiment and specification work.
