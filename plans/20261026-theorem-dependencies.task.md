# Compiled theorem dependency report

Date: 2026-10-26. Status: DONE. Audience: the implementation team.
Owner request: implement the investigated dependency exporter and local report
to support the current theorem and proof refactoring work.
Record: [status](20261026-theorem-dependencies.status.md).

## Required outcome

A repeatable command exports dependencies from compiled Lean declarations and
produces a self-contained, searchable HTML report. The default report covers
the model, codec, text translation, surface API, and conformance library of the
selected build. An explicit module manifest supports other compiled modules,
including test or experiment modules. The report lists selected modules,
loaded coverage, source provenance and exclusions. A missing selected artifact
fails clearly; incomplete coverage must not be reported as complete.

Each project declaration has an exact kernel name, owning module, declaration
kind, private/internal flags, and source selection when available. Separate
edges represent references in its type and its proof/value. External targets
remain identifiable. Private and generated helpers remain in the raw data.
The report can fold internal helper paths, show the intervening declarations,
and distinguish such paths from direct edges. It can inspect dependencies,
users and transitive paths without requiring a server or a new graph database.

The report supports module-level dependency summaries and refactoring views
for wrapper candidates, frequently referenced theorems, matching dependency
neighbourhoods and declarations with no project consumers. These are candidates
for inspection, not claims of redundancy or safe deletion. Existing proof-cost
data can be attached when supplied; missing measurements stay explicit.

The documentation explains how to generate and open the report, select scope,
and interpret it. References in the current elaborated proof do not establish
logical necessity. Discarded tactic searches, anonymous proofs that do not
survive compilation and module rebuild causality are outside this graph.

## Acceptance checks

A Nix check runs the real exporter on a compiled Lean fixture. It checks a
statement-only dependency, a tactic-selected proof dependency, a private helper,
a generated helper path, an external reference and a separately selected module
that the main fixture does not import. Source locations, exact private names,
deterministic output and missing-module failures are checked. The checked report
retains all helper nodes and labels type and body edges separately.

Graph/report tests exercise incoming and outgoing paths, cycles, folded helpers,
module summaries, refactoring candidates and safely embedded HTML data. Browser
interaction checks exercise search, selection, direction, helper expansion and
source navigation where the available browser supports local artifacts. Tests
have explicit timeouts. A Nix report over the real compiled packages supplies
integration evidence and a usable artifact for the owner. Standard repository
commit review and task-completion checks apply; semantic mutant suites are
unchanged.

## Relevant code and constraints

Base: integration commit `6413afe3ff50`, Lean 4.34.1. Work is isolated in
`sqlite-verifier-theorem-dependencies`. Reuse the metadata design in
`packages/public-doc-tools/PublicDocInventory.lean`; documentation coverage's
public-only filtering must not remove graph nodes. Lean imports need private
data, and theorem bodies require `value? (allowOpaque := true)`.

Declaration ownership comes from the environment's module index, not a name
prefix. Type and body references can overlap. Helper folding must preserve
reachable theorem paths and terminate on cycles. Source positions can be absent
and internal names are not reliable source locations. Library module enumeration
must include selected modules outside umbrella import closures. Build integration
uses the existing filtered Nix inputs and does not change semantics or the judge.

This is one implementation slice. Production theorem refactoring and adoption
of Beam or an LSP service are separate work.
