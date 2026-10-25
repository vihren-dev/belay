# ADR17: complete surface and guide acceptance

Created 2026-10-24. Status: OPEN. Final acceptance follows all required slices.
Status: [progress](20261024-adr17-guide-acceptance.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), its accepted clarifications
and explicit deferrals; [ADR 0016](../docs/adr-0016-model-and-surface.md).

## Purpose and boundary

Individual slices prove their own contracts. This task checks that the completed
surface works as one installed library, that the guide states its actual
meaning, and that no required capability remains only a proposal. It closes
ADR17 only after that evidence and the completed task publications exist.

The product guide remains in the private product repository. Its README forbids
copying its content into the public code repository or linking back to it.
Use private records for a guide inventory and its exact source validation.
Public tests and docs state engineering contracts in their own words and must
not import or fetch private files. No general documentation generator, new
benchmark service or extra SQL interpreter is part of this acceptance task.

## Required outcomes

- **One accurate capability inventory.** Account for S1 through S8, editor
  features, checked SQL doc blocks and proof-cost reporting. Each required
  behavior maps to its implemented public declaration or tool, accepted task
  and Nix-selected test. The inventory distinguishes implementation from
  proposals and tests from unchecked examples. An unimplemented required row
  prevents completion. Only explicit ADR deferrals remain deferred; do not
  silently add a new deferral to make the inventory pass.
- **The guide describes the installed surface.** Reconcile the published
  profile/header corrections, the S4 guide work and earlier S2/S3 corrections
  that remain in the product workspace. Preserve the accepted defaults, query
  shapes, parameter rules, error continuation, unmodeled termination, full
  execution equivalence and other owner decisions. Incorporate the later
  accepted observation-view and contextual-pairing contracts from ADR17 D1.
  Include the accepted explicit fresh-run helper and interface-scoped simulation.
  Claims about the same API agree across prose, examples, tables,
  the complete example and resolved-question notes.
- **Examples check their stated claims.** The complete example compiles against
  the installed surface with its actual SQL files and doc blocks. Smaller
  fragments have explicit surrounding declarations where needed. Examples of
  false claims produce certified counterexamples; expected diagnostics are
  checked as diagnostics, not admitted proofs. Prove the final universal
  examples with their accepted schema/effect premises. Do not substitute a
  fixed database, assume the desired postcondition, weaken a claim to True,
  skip a difficult example or use sorry/native proof axioms to pass the check.
- **Readers can reproduce the workflow.** An ordinary consuming Lake package
  imports Belay, binds parameters, builds its external SQL inputs, uses a
  generated query module, proves a success claim and a triple, and checks a
  counterexample. Its freshness/proof-cost tools run as documented. Installed
  dependencies and paths work outside the source checkout. Existing S7 consumer
  fixtures supply this evidence where they already cover the behavior; add only
  missing integration coverage, not another equivalent build harness.
- **The four levels remain different.** Demonstrate a schema-resolved statement
  that fails for data, a successful migration that loses observable rows, and
  a locally correct call pairing that does not establish whole-program behavior
  without the required context/invariant conditions. Preserve the existing
  native and kernel counterexamples that motivated corrected claims. Neither
  finite search nor one canonical result is a universal proof.
- **Trusted and untrusted work remain separated.** The checker and tactics
  produce kernel-checked proofs or refutations; parsing, sampling, native replay,
  displayed suggestions and editor services do not supply axioms. Audit the
  final example theorems and their dependencies. The model and conformance
  runner retain their declared dependency boundaries. Public explanations of
  defaults, supported SQL, proof scope and known restrictions match the final
  source and frozen conformance claims.
- **No stale implementation path survives.** Replaced interfaces and the old
  validity-decision fallback have no remaining production caller or misleading
  guide explanation. Temporary prototypes stay explicitly test-only or are
  removed when production tests supersede them; neither is a public alternate
  semantics. Avoid unrelated cleanup. Final task/status records identify the
  checked revisions, required publications and remaining explicit deferrals.
- **Completion is reviewable and published.** Publish coherent implementation
  and guide changes with their acceptance evidence. Keep judge changes in
  separate protected PRs, whose merge requires the owner. The owner's standing
  authorization covers pushing ready work; it does not authorize merging those
  PRs. Preserve unrelated product history when publishing guide fixes. Clean
  only completed, pushed workspaces under the standing cleanup authorization.

## Validation and acceptance

Use the actual installed pinned library and SQLite runtime. Public feature
acceptance remains in Nix-selected tests and existing frozen verdicts. Private
guide validation records its exact revision, commands and public artifact
identities privately; do not upload private source or derived private contents
to a public cache or artifact. Private documentation checks do not replace the
public Nix evidence for an implementation claim.

Compile the complete example and required fragments, check the intended output
or diagnostic of each, recheck generated proof suggestions and counterexample
regressions, and audit theorem dependencies. Reject `sorryAx`, `ofReduceBool`,
`_native` and assumed model soundness. Use existing compiler/editor/consumer
test support with finite timeouts. Focus tests on cross-feature behavior not
already established by the individual task suites.

Each coherent implementation or specification change has its focused checks
and independent review; documentation changes validate their source and scope.
After the integrated final review, one acceptance boundary runs `just test-full`
and `just verdict`, then `just test-nix` and `just test-scheduled-checks`. The
last command follows the owner's override in
[the build-boundary status](20261024-text-build-boundaries.status.md).
Compare frozen predictions and locked claims; a changed corpus or claim follows
the separate judge workflow. Record the final Nix outputs and exact revisions.

## Prerequisites and coordination

This task consumes the completed S4/S5/S6/S7/S8 contracts, required model work,
editor task, doc-block task and measured proof-cost implementation. At task
creation, most of these were active or specified without implementation.
Production S6 now has execution, assertion, migration-pattern and automation
tasks; S8 has a full-state/scoped simulation task. Production proof costs still
await the collector prototype. This final gate does not claim those inputs are
implemented.

Reserve the final integration workspace and the private guide edit surface
before work. The current guide owner must finish or explicitly hand off first.
The final audit may discover a narrow integration fix; report a genuine new
semantic/specification contradiction before changing its meaning, and continue
unaffected validation. A missing substantial feature returns to its specified
task rather than becoming an unrecorded implementation inside this audit.
Honor the temporary ban on herdr review tabs before Monday, 2026-10-26 UTC.
