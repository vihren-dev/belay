# Resolver certificate task status

Date: 2026-10-28. Status: DONE on publication of this reviewed completion record.
Audience: the implementation team.
Task: [shared resolved-statement certificate](20261028-resolver-certificate.task.md).
Specification: [ADR 0026 D3](../docs/adr-0026-semantic-proof-boundaries.md).
Assignment source: `5dc38c0a`, including preservation-context implementation
`1773d573` and its reviewed handoff `5a0c9b32`.

## Completion record

Final implementation source is `23a3427b`, published as `9eb179de` in [PR
297](https://github.com/vihren-dev/sqlite-verifier/pull/297). The [combined
acceptance record](20261028-proof-refactor-ci.status.md) owns the final Nix
reports and source identities.

One certificate replaces three syntax dispatches while retaining unconditional
after-state equality, arbitrary-limits linkage and conditional
current/saved-state validity.

Original-formula witnesses passed Nix at `53a346e1` before redundant copies
were retired. Final `23a3427b` passed the full suites, verdict, configured Nix
checks, scheduled writers, public documentation and API reference. Final
dependency inspection and the [Nix cost sample](20261028-expression-congruence.status.md#final-nix-proof-cost-sample)
complete the shared measurements. The [goal ledger](../docs/lean-simplification-goal.md#milestones-and-decisions)
records 87,018 maintained Lean lines and all 30 fixed capability groups retained.

The implementation and retirement are published. Integration and publication of
this reviewed closing record complete this task. The separate CI task still
awaits hosted mutation measurements. Record checks: `tests/docs_test.py` and
independent `just review`. Following sections preserve historical checkpoints;
their pending notes are superseded by this completion record.

Final Nix resolver acceptance covers all 11 mutants in six groups, with no
failure, error or skip and unchanged 300-second test limits. JUnit:
`/nix/store/ph0mnmjkvijlfwijmyk0vbllmmbnfi1j-sqlite-verifier-test-mutants-ci-repair-1/junit.xml`.
The command completed in 511.442 seconds; each mutant compiled and changed an
authored target verdict.

## Assignment audit

The coordinator read the three current dispatches, applied-catalog and
complete-run consumers, statement equations, direct-call search and existing
resolver test owner. The three independent premises, control/saved-catalog
distinction and source/trace split match the governing specification.

The direct-call inventory matches the current source. The preservation-context
implementation changes its shared condition application but retains the
schema-link consumer and every-complete-execution guarantee. No owner-level
specification decision was identified.

The task reuses the existing admitted-resolver, schema/script, name-trace,
conformance-trace and resolver-mutant test owners. The CI repair now partitions
eleven resolver mutants into six source-file groups without dropping cases.
No new runner or permanent per-constructor test matrix is assigned.

Assignment commit `969b6d77` passed independent Claude review with zero must and
zero should findings (`reviews/20261028T130545Z-969b6d77`). The prior review's
status-heading ambiguity was fixed and recorded. The assigned worker completed
its source audit and found no mismatch;
implementation is released. No implementation acceptance is recorded yet.

Implementation, local original-formula diagnostics and independent review are
complete. The reviewed source is integrated in the coordinator. Pending:
integrated Nix acceptance, temporary witness retirement and push.

## Implemented source

The three dispatches are replaced by `resolveStatement_certificate`. Its
`after`, `link` and `valid` fields keep the original independent assumptions.
`ResolverCertificate` owns the two shared catalog/write transports; the single
syntax split for these three guarantees remains in `ResolveStatementFacts`. Rename and DROP COLUMN reuse
their existing outcomes, and INSERT SELECT reuses its form and catalog facts.
Prepare errors, write rules, transaction catalogs and settings keep their formulas.

`ResolveState.Valid` moved unchanged into the lowered `ResolveStateSpec`, beside
`after` and its ordinary-statement equation. `SchemaLink` remains in Forms.
Link no longer imports the former validity dispatch. All direct callers use the
certificate fields; applied-catalog validity still includes controls and settings.
ScriptRunLaws and the fold/effect consumers import their proof provider explicitly.
Live ADR 0022 references now name the corresponding certificate fields.

The coordinated shared-file window added only the ResolverCertificate import and
its explicit model module entry. Model roots and all other module entries remain
unchanged. No executable resolver or statement-equation implementation changed.

The existing admitted-resolver test owner contains one temporary copy of the
three old dispatch signatures and the full applied-catalog validity signature.
It audits the generic certificate instead of the deleted validity dispatch and
retains all independent leaf checks. These four projections remain until final
Nix acceptance; retire redundant formulas afterward, keeping concise independent
field premises and current/saved catalog meaning in this same owner. No new test
runner, constructor matrix or suite registration was added.

Local diagnostic logs are under `/tmp/adr26-d3-*`. They do not establish Nix
acceptance. Diagnostic commands covered the core certificate, script/catalog
projections, full package build and affected fixtures. Independent review is
recorded below. Final integrated Nix and resolver-mutant
acceptance remain with the coordinator; this task is not DONE.

## Diagnostic scope before review

Development commands included `just dev-build`, the existing admitted-resolver,
schema/script, name-trace and conformance-trace owners, and source/layer checks.
A missing explicit ScriptRunLaws proof import was repaired. The final matched
Nix dependency report supersedes the earlier local closure inspection.

After the review documentation corrections, the change removes 85 textual
production Lean lines, including the new 85-line certificate owner, moved
definitions and caller/import changes. Every
changed semantic source module is below 200 lines; the existing Model umbrella
remains the established exception. The existing Python test owner adds 18 lines,
including 16 embedded Lean witness lines; standalone Lean fixtures are unchanged.
These raw line differences do not substitute for the goal's Nix/scc count.
No capability loss or timing improvement is claimed.

## Independent review corrections

Claude reviewed implementation `01065389` in `20261028T131854Z-01065389`:
zero must findings and three should findings. The reviewer did not run checks.
All three are fixed: DropSpec and TriggerDefinitionSpec name the new dispatch
owner, and both certificate modules now explain their role in module docstrings.
The corrections change no declaration type or proof body. The follow-up
diagnostics repeated `just dev-build`, source checks and the
resolver contract/axiom fixture. Claude reviewed correction
`027bf6c6` in `20261028T132547Z-027bf6c6`, with zero must and zero should findings.
The reviewer read the correction and did not run checks. These results remain
local diagnostics, with integrated Nix and resolver-mutant acceptance pending.

## Frozen implementation handoff

Implementation: `01065389ba958188a5d092b517ed056be9b52849`.
Documentation corrections: `027bf6c6c846d0b15ac99dbc66698a6554004e41`.
The final handoff commit adds only this status update and the unchanged review
record. The coordinator can integrate this source while retaining the four
migration formulas and all ADR 0025 witnesses. No Nix suite, push, PR or review
tab was started by this worker. Keep the workspace until integrated acceptance
and push are confirmed. Mark the task DONE only after acceptance and retirement.

## Coordinator integration

Reviewed handoff `6cb1cc55` merged with the current coordinator without source
conflicts. Development diagnostics used the combined build and documentation/
layer checks. The coordinator checked the complete manifest against source:
872 explicit model modules,
exactly one addition (`ResolverCertificate`), unchanged codec registrations and
all 19 public roots. No formula or proof changed during integration.
The build log is `/tmp/proof-refactor-resolver-integration-dev.log`.
Final combined Nix acceptance remains pending.

## Final-contract witness retirement

The coordinator confirmed final affected-contract Nix acceptance at
`53a346e1899f7221c67faa3c6df379862e16edb8` before this retirement.
The accepted formulas remain replayable at that revision; the
[combined acceptance record](20261028-proof-refactor-ci.status.md) records the Nix evidence.
This entry supersedes the earlier pending-acceptance notes.

The temporary after-state, next-validity and applied-catalog projections are
retired from `admitted_atoms_resolver_facts_test.py`. Its arbitrary-limits
schema-link assertion remains as a current independent-premise check: supplied
limits need not match the context, and no execution-mode or saved-validity
assumption is available. `resolveFrom_after` and `Connection.resolveState_after_next`
retain unconditional state equality; `resolve_valid` retains arbitrary valid
saved states; `resolveStatement_appliedValid` retains all statements, including
controls, and the distinction between `applyCatalog` and the next catalog.
Leaf contracts and the generic certificate axiom audit remain.

Affected existing check: `admitted_atoms_resolver_facts_test.py`.

Independent Claude review of `ca180788` reported zero must findings and one
should finding. The finding is fixed: these acceptance records omit local
diagnostic results, as required by `AGENTS.md`.
The coordinator integrated reviewed retirement `e3ae5e92` with the current
proof branch. Package and test sources match that reviewed retirement exactly;
the other integration changes are documentation and review records only.
Retirement Nix acceptance and push remain pending.
No production package, execution semantics or capability changes in this cleanup.
