# Expression congruence task status

Date: 2026-10-28. Status: IN PROGRESS; implementation reviewed, Nix acceptance pending.
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
- Pending: Nix acceptance and net source measurement,
  temporary witness retirement, integration and push. The shared contract and
  focused fixtures add maintained code; no size or build-time saving is claimed.
  No implementation acceptance is recorded by the historical experiment.
