# Expression congruence task status

Date: 2026-10-28. Status: IN PROGRESS; implementation accepted, retirement review and integration pending.
Audience: the implementation team.
Task: [shared expression congruence](20261028-expression-congruence.task.md).
Specification: [ADR 0026 D5](../docs/adr-0026-semantic-proof-boundaries.md).
Source baseline: `9ead5e38`; original target formulas match `3e2212ed`.

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
- Integration `a3dd5a9a`: the complete four-package development build and 19
  source checks passed as diagnostics. Independent Claude review reported zero
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

## Integrated proof-cost diagnostic

At production source `a7eddc9d`, a one-time native Lean 4.34.1 profiler run
measured nine shared proof owners after integration. Source copies were unchanged;
source hashes and the selected compiled-artifact hashes were checked before and
after. The repository and its caches were not modified. This is a local cost
diagnostic, separate from Nix acceptance and from the source-size goal.

| Representative body | Internal heartbeats |
| --- | ---: |
| `runSqlFrom_holds` | 199,107 |
| `runScriptAllFrom_holds` | 305,666 |
| `resolvedStepOutput_query_source` | 313,444 |
| `resolvedStepOutput_query_isError` | 525,388 |
| `resolvedStepOutput_selectOne` | 631,459 |
| `subqueryContext_agrees` | 271,300 |
| `resolveStatement_certificate` | 1,620,488 |
| `Expr.evaluate_congr` | 7,229,249 |
| `observationProfile_eq_iff` | 40,759 |

The run used one thread, `Elab.async=false`, native profiler heartbeats and the
`Elab.definition.value` trace. Its threshold was `9007199254740991` to suppress
other profiler nodes. Two profiled repetitions produced identical body counts.
These are internal heartbeats, not the compiler's budget units; they cover body
elaboration, not total kernel checking or package build cost.
After control/profile warmups, the sample order was control/profile/profile/control.
The sum of nine whole-file medians was 8.085 seconds without profiling and
8.617 seconds with it: 6.58 percent observed overhead in this small, noisy sample.
There is no comparable pre-migration measurement and no speedup claim.
Raw logs, unchanged source copies, options and hashes are in
`/tmp/adr26-proof-costs-20261028/measurements.json` and its containing directory.
No collector import, permanent benchmark or measurement gate was added.

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

The cleanup removes only temporary fixtures and their inputs. A bounded diagnostic
run checked the six changed Python test owners plus `test_test_ownership.py` and
`docs_test.py`: 34 cases passed. It used independent copies of the coordinator's
compiled libraries with `LEAN_NUM_THREADS=2`; it is not Nix acceptance.
The log is `/tmp/adr25-26-retirement-diagnostics.log`.

Retirement Nix acceptance, independent review, integration and push remain pending.
No production package, execution semantics or capability changes in this cleanup.
