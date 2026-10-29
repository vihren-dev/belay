# Expression congruence task status

Date: 2026-10-28. Status: DONE on publication of this reviewed completion record.
Audience: the implementation team.
Task: [shared expression congruence](20261028-expression-congruence.task.md).
Specification: [ADR 0026 D5](../docs/adr-0026-semantic-proof-boundaries.md).
Source baseline: `9ead5e38`; original target formulas match `3e2212ed`.

## Completion record

Final implementation source is `23a3427b`, published as `9eb179de` in [PR
297](https://github.com/vihren-dev/sqlite-verifier/pull/297). The [combined
acceptance record](20261028-proof-refactor-ci.status.md) owns the final Nix
reports and source identities.

One mutual argument replaces four equality proof paths, retaining
value/fault/subtype and strengthening both context laws without removing
independent caller premises.

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

Closing decision `0cd4cbf5` has independent Claude reviews
`20261028T173427Z-0cd4cbf5`, `20261028T173759Z-0cd4cbf5` and
`20261028T174057Z-0cd4cbf5`, each with zero must and zero should findings.
The supplements checked immutable evidence and governing completion clauses
that the first review omitted. These records are retained under `reviews/`.

## Assignment

The owner authorized ADR 0025/0026 implementation on 2026-10-28. This task is
assigned to the CI repair worker after its reviewed handoff. It owns expression
congruence and its direct consumers, disjoint from the active atom-preservation
and source-agreement workers. Shared registrations require coordinator sequencing.

## Progress and evidence

- Assignment: inspected all four current target proofs, their direct consumers,
  the existing claims fixture runner and the historical expression experiment.
  Confirmed the target files have no source difference from `3e2212ed`.
- Assignment commit `10f933eb`: independent Claude review found zero must and
  zero should findings (`reviews/20261028T115346Z-10f933eb`). The coordinator
  checked the baseline with `jj`; the reviewer could not check it with Git.
- Implementation: `ExprCongruence` owns primitive read agreement, one mutual
  evaluator induction, and the row/parameter specialization. It compares the
  value/fault pair and JSON subtype. Primitive cases keep separate existence,
  scalar-first and membership-row observations; argument evidence keeps the
  head/tail results that lazy IIF observes.
- `EvalContextLaws` owns the moved RowFree, withRuns and certainFirst definitions
  and their existing projection laws. `ExprAppendLaws`, `ExprContextLaws` and
  `RowwiseExpr` use the shared result. The four duplicated equality inductions
  are removed. The append value API and separate Rowwise fault/calmness laws
  retain their formulas. SelectOne consumers retain their independent calmness
  and fault-freedom premises.
- The two context laws now preserve subtype and allow fallible calls. The
  certainty law still excludes scalar subqueries. The public umbrella and
  explicit globs include the two lower modules; native public roots are unchanged.
- Checks: `tests/surface_claims_test.py` owns the stronger universal formulas,
  malformed local JSON, distinct certainty/subtype observations and lazy-operand
  faults. It audits the shared evaluator theorem and independent syntax evidence.
  `ClaimsExpressionCongruenceMigration.lean` keeps the four original formulas
  temporarily. Existing EXISTS, IN, failing-condition and scalar claims remain
  in that same test owner. No new runner or Nix source owner was added.
- Development commands: `just dev-build` and the existing claims test owner.
  These are diagnostics; acceptance requires the coordinator's combined Nix
  package, public documentation, consumer, conformance and full-suite checks.
- Implementation commit `facc67dc`: independent Claude review found zero must
  and zero should findings (`reviews/20261028T121805Z-facc67dc`). Source is frozen
  for the coordinator's combined acceptance run.
- Integration `a3dd5a9a`: development diagnostics used the complete four-package
  build and source checks. Independent Claude review reported zero
  must and zero should findings (`reviews/20261028T124800Z-a3dd5a9a`), but could
  inspect the manifest resolution only partially. The coordinator separately
  checked that its 872 explicit modules exactly match the source, that only the
  two D5 modules were added, and that all 19 public roots are unchanged.
  This integration is later than the first frozen Nix acceptance snapshot;
  D5's Nix acceptance remains pending.
- The coordinator reconciled the specification status headers on 2026-10-28.
  The agreement documents now record D2 and D5 as implemented with final
  acceptance pending. Their semantic requirements and baseline targets remain
  unchanged; other proof specifications distinguish active and deferred work.
- Status reconciliation `d7fc3011` received independent Claude review
  `20261028T131611Z-d7fc3011`: zero must and zero should findings. The
  coordinator also checked the retained D7 deferral against ADR 0026.
- Pending: Nix acceptance and net source measurement,
  temporary witness retirement and push. The shared contract and
  focused fixtures add maintained code; no size or build-time saving is claimed.
  No implementation acceptance is recorded by the historical experiment.

## Final Nix proof-cost sample

The one-time sample at `23a3427b` completed in 52.907 seconds. Its immutable
`measurements.json`, source/artifact hashes and raw traces are in
`/nix/store/8mzc56z463p8pzcf95ccbzxij6c14a9k-sqlite-verifier-adr26-final-proof-cost-sample`.
Pinned Lean 4.34.1 ran with one thread and `Elab.async=false`: one control and
profile warmup, then two measured runs of each. It reported 50 definition-body
nodes across nine owners. These include definitions and mutual declarations;
they are not a count of independent proofs.

| Owner | Representative body | Internal heartbeats | Control file median, seconds |
| --- | --- | ---: | ---: |
| RunHolds | `runSqlFrom_holds` | 199,107 | 0.391 |
| ScriptRunHolds | `runScriptAllFrom_holds` | 305,666 | 0.382 |
| QueryOutputFacts | `resolvedStepOutput_query` | 408,907 | 0.429 |
| QueryStatementOutput | `resolvedStepOutput_query_hasRows` | 644,277 | 0.469 |
| SelectOneOutput | `resolvedStepOutput_selectOne` | 631,459 | 0.360 |
| SourceAgreement | `subqueryContext_agrees` | 271,298 / 271,300 | 0.543 |
| ResolveStatementFacts | `resolveStatement_certificate` | 1,620,488 | 0.443 |
| ExprCongruence | `Expr.evaluate_congr` | 7,229,249 | 4.641 |
| ExecutionProfile | `observationProfile_transport` | 95,568 | 0.338 |

Body heartbeats measure elaboration within the named profiler node. Whole-file
wall time includes other compiler work; neither is whole-package build cost.
Two repeated bodies differ by two or four internal heartbeats; all raw samples
are retained. There is no comparable pre-migration timing baseline or speedup
claim. The [combined acceptance record](20261028-proof-refactor-ci.status.md)
records producer build phases separately, with their cached prerequisites.
No permanent benchmark or measurement gate was added.

## Final-contract witness retirement

The coordinator confirmed final affected-contract Nix acceptance at
`53a346e1899f7221c67faa3c6df379862e16edb8` before this retirement.
The accepted formulas remain replayable at that revision; the
[combined acceptance record](20261028-proof-refactor-ci.status.md) records the Nix evidence.
This entry supersedes the earlier pending-acceptance notes.

The four-formula migration file and its driver entry are retired. Its full
append value/fault/subtype assertion moves to `ClaimsExpressionCongruence.lean`
as a current boundary check, because downstream append clients use only values.
The existing stronger context assertions, fallible local JSON, separate first/row
certainty, lazy operands and subtype counterexample remain. Rowwise's query consumer for arbitrary
contexts and independent fault-free theorem retain its guarantee.
The same three generic/independent axiom audits remain.

Affected existing check: `surface_claims_test.py`.

Independent Claude review of `ca180788` reported zero must findings and one
should finding. The finding is fixed: these acceptance records omit local
diagnostic results, as required by `AGENTS.md`.
The coordinator integrated reviewed retirement `e3ae5e92` with the current
proof branch. Package and test sources match that reviewed retirement exactly;
the other integration changes are documentation and review records only.
Retirement Nix acceptance and push remain pending.
No production package, execution semantics or capability changes in this cleanup.
