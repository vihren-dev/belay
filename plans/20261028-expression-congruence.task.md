# Share expression congruence proofs

Date: 2026-10-28. Status: DONE on publication of this reviewed completion record.
Completion: [final acceptance record](20261028-expression-congruence.status.md#completion-record).
Audience: the implementation team.
Specification: [ADR 0026 D5](../docs/adr-0026-semantic-proof-boundaries.md),
[agreement requirements](../docs/spec-proof-agreement.md) and
[exact targets](../docs/spec-proof-agreement-targets.md).
Record: [status](20261028-expression-congruence.status.md).
Source baseline: `9ead5e38`; the four target formulas equal main `3e2212ed`.

This task contributes to the [Lean simplification goal](../docs/lean-simplification-goal.md)
through shared proof reasoning and removal of replaced inductions. Include the
common contract, adapters and tests in net counts; the historical experiment
does not establish net savings. All baseline capabilities and existing client
guarantees remain required. No capability loss is authorized.

## Required behavior

One mutual expression/argument induction establishes equality of expression
value, fault and JSON subtype when its allowed primitive observations agree.
The comparison can use different contexts and rows. A mask can restrict nodes
through the existing expression traversal; no minimal-read algorithm is required.

Primitive observations cover column positions, parameters, counters, clocks,
aggregates and the projection appropriate to each subquery use. Existence uses
emptiness and fault. Scalar use uses the first value and the fault sensitive to
first-row certainty. Membership uses first-column values and the fault sensitive
to row-set certainty. Preserve those distinct certainty rules. Date calls may
conservatively require equal clocks. Lazy scalar calls retain the operand results
they inspect; JSON subtype remains part of the conclusion.

The common argument replaces the equality inductions behind these four
declarations in `Belay.Sqlite.Model.Resolved`:

| Owner | Declaration | Required guarantee |
| --- | --- | --- |
| `ExprAppendLaws` | `Expr.evaluate_append` | Recover its exact value/fault/subtype formula, with its existing width, bound and `RowFree` assumptions. |
| `ExprContextLaws` | `Expr.evaluate_withSubqueries` | Preserve value, fault and subtype when subquery runs agree at the evaluated row, without the old no-fallible-call premise. |
| `ExprContextLaws` | `Expr.evaluate_certainFirst` | Preserve value, fault and subtype after marking first rows certain, without the old no-fallible-call premise; keep the scalar-subquery exclusion. |
| `RowwiseExpr` | `Expr.Rowwise.evaluate_congr` | Recover equality from equal rows and parameters through a syntax-to-locality adapter. |

Expose a read-locality specialization that admits arithmetic, casts, JSON and
scalar calls when their reads are confined to the row and parameters. Existing
`Expr.Rowwise` expressions satisfy that contract through a small syntax proof.
Keep `Expr.Rowwise.fault_none` and `Expr.Rowwise.calm` with their separate, narrower
hypotheses. A local expression can fault. Preserve the separate truth/complement
laws in `RowwiseExpr`.

Keep `Expr.eval_append` with its current name and exact formula for its actual
consumers. Its proof projects the shared result. Useful specialized laws may
retain semantic names and short proofs through the common argument. Remove
duplicated equality inductions and obsolete wrappers; keep no parallel old API
or aliases. The stronger context laws are current guarantees.

## Ownership and boundaries

The assigned owners are the three target files, suitable lower domain modules
for the common argument and locality facts, and direct context-law consumers
`SelectOneSubqueryOutput`, `SelectOneRowsOutput` and `TwoStateNotExistsExcept`.
Move `EvalContext.RowFree`, `EvalContext.plain_rowFree` and
`SubqueryRun.certainFirst` below their consumers without duplicate definitions.
Retain the useful `withRuns` and `certainFirst_*` projection laws, including simp
registrations. Keep modules below 200 lines and use concrete domain owners.

`Resolution/ColumnDropExprLaws` proves a different transformation: its expression
and row both change. Preserve `Expr.evaluate_dropColumn` and `Expr.eval_dropColumn`
and their `RowFree` dependency; they are not a fifth fixed-expression replacement.
`SimpleQueryAppend`, `CertifiedQueryOutputs` and the read-certificate clients
retain their completed shared proofs, per-branch obligations and differing table
positions. Preserve ADD COLUMN, derived-column and derived-lookup clients of
`Expr.eval_append`. The ADR 0025 worker owns changes to key and atom proofs;
coordinate any necessary import-only repair instead of editing those files
concurrently. The source-agreement worker owns `Resolution/QueryForm` and
two-state source/statement laws; this task does not need those files.

Do not change expression evaluators, accepted SQL, conformance inputs, judge
claims or admission rules. Removing an unnecessary congruence premise does not
remove independent calmness, fault-freedom, resolution, clock or counter
restrictions in callers. Update checked documentation with the precise stronger
formulas. The common proof must not depend on the replaced equality inductions.

Model aggregation and manifest registrations are shared. Ask the coordinator
for a short ownership window before editing them. Reuse the existing
`tests/surface_claims_test.py` owner and fixture helper for missing focused
checks; coordinate any `build-support/tests.nix` source inputs with the owner
of that file. No new fixture runner or general proof framework is required.

## Acceptance checks

- Kernel-check the four original formulas with their baseline assumptions and
  both stronger context formulas. Include a fallible local JSON call that the
  old hypothesis excluded. Universal proofs establish the contracts; examples
  do not replace them.
- Keep focused coverage of scalar first certainty, membership row-set certainty,
  lazy scalar operands and JSON subtype. Check that equal value/fault pairs
  alone do not imply subtype equality. Include an expression that is local but
  not Rowwise and a local expression that can fault. Reuse existing examples
  wherever they already protect the required meaning.
- Audit the shared proof and independent locality evidence with the existing
  forbidden-axiom checks, without duplicate audits of projections. Inspect
  imports, instances, simp and export registrations before deleting names.
- Nix compiles the complete affected packages and checked public documentation.
  Preserve existing claims fixtures for EXISTS, IN and potentially failing
  conditions, purge-frame assertions, derived-column examples and DROP COLUMN
  conformance. Preserve all consumer premises not changed by the approved
  context-law strengthening.
- Report net Lean changes including the common argument, masks, adapters,
  callers and tests. Do not infer a build-time improvement from source size.
  Apply the repository's per-edit, per-commit, end-of-slice and end-of-task
  checks with timeouts; use the coordinator's shared full Nix build slot.

The four old-formula witnesses are temporary migration evidence. After final
Nix acceptance, remove redundant witnesses and registrations and record the
accepted historical revision for replay. Retain unique premise/trust checks
until covered by a current consumer or focused regression. Keep tests of the
stronger contracts and distinct semantic observations. Add no permanent old/new
equivalence matrix or dependency snapshot test.

The task is done when the changes, acceptance evidence and test retirement are
committed, independently reviewed, integrated and pushed.
