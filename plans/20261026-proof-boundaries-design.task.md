# Experiment with shared semantic proof boundaries

Date: 2026-10-26. Status: ACTIVE.
Audience: the implementation team.
Owner request: run experiments, then specify the proof refactor justified by
their results. Record: [status](20261026-proof-boundaries-design.status.md).
Related: [ADR 0025](../docs/adr-0025-compositional-preservation-proofs.md).

## Required result

An isolated workspace contains reproducible experiments and reviewed design
specifications for the additional opportunities found in the theorem dependency
report. Production behavior and production proof declarations remain unchanged.
The experiments assess query output contracts, source agreement across current
and initial databases, resolver result certificates, row-engine state/stop
contracts, observation equivalence, and expression evaluation congruence.
They also assess the import ownership that makes general facts hard to reuse.
Each candidate receives an evidence-based adopt, narrow, or defer decision.
A failed or larger-than-useful abstraction is a useful result and is recorded.

Accepted candidates have small kernel-checked prototypes against the pinned
production libraries, applications to existing claims, and explicit limits on
what was established. A prototype must demonstrate the proposed shared reasoning;
wrapping the original specialized theorem does not establish consolidation.
Representative applications retain their original mathematical assumptions.
Source inventories distinguish affected code from measured net savings. Timing
claims require measurements and must distinguish loading, elaboration and rebuild
scope; no timing improvement is inferred from fewer graph nodes or source lines.

The resulting proposed ADR and implementation specifications state observable
outcomes, formula/trust obligations, relevant existing boundaries, and acceptance
checks. They contain no prescribed implementation sequence. They distinguish
the additional work from ADR 0025 and document dependency order where necessary.
Implementation task files are created only when work is about to be assigned;
this design task supplies the specifications without a speculative task backlog.

## Acceptance evidence

A standalone Nix experiment target compiles the accepted Lean prototypes and
their representative applications against the selected model/surface packages.
Compiler errors or warnings fail the target. The check records the explicitly
audited proof closures and rejects axioms outside `propext`, `Classical.choice`,
and `Quot.sound`. No `sorry`, native evaluator axiom or new trusted shortcut is
accepted. Every subprocess has a timeout. The experiment target is explicit,
with no new production CI suite or runtime dependency.

Representative applications cover the distinctions the abstraction could erase:
source absence and pragma dependence; possible outputs and errors; weak versus
full observations; resolver validity assumptions and transaction snapshots;
FAIL versus rollback, permitted work and FK phase boundaries; expression faults,
JSON subtype and subquery certainty as applicable to the chosen prototypes.
The record states any unproved extension rather than presenting it as delivered.

The new source and specifications receive the repository's independent commit
review. Existing required Nix checks remain applicable; unchanged check inputs
can reuse their existing store results. The final source diff confirms no edits
to production packages, runtime/build integration, judge inputs or corpora.

## Relevant boundaries

The frozen production source is report revision `3fe5caef`; the workspace also
includes prior design revision `0cadcde9`. The report examines compiled constant
references, not source-level simp registrations, exports or all test consumers.
Generated declarations and zero-consumer nodes alone do not justify deletion.

`NestedRun.Keeps` accepts a database predicate, but FK success and stop contracts
also describe counters and permitted work. Their invariants need not hold at
every internal instruction. Query output families have different premises for
row characterizations and no-error claims. `TwoStateReads` and
`TwoStateCurrentLaws` duplicate source/context traversals; pragma rows can depend
on the database. Resolver state equality is less conditional than validity.
Expression evaluation also computes faults and JSON subtype information.
Observation equality alone does not justify arbitrary sequential composition.

Keep existing semantics and useful independent guarantees. The project has no
users; accepted implementation specifications replace obsolete declarations and
update callers without compatibility aliases. General helpers should have actual
consumers and an import owner below their specialized uses.
