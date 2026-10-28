# Source agreement and expression congruence

Date: 2026-10-26. Status (2026-10-28): D2 implemented; acceptance pending. D5 remains proposed.
Audience: implementers and reviewers.
Decision: [ADR 0026 D2 and D5](adr-0026-semantic-proof-boundaries.md).
Evidence: [source and expression findings](../experiments/proof-boundaries/source-expression-findings.md).
Targets: [source helpers, expression proofs, definitions and callers](spec-proof-agreement-targets.md).
Source-checked against production revision `3e2212ed6983` on 2026-10-28. The fourteen
source helpers and four expression targets keep their previous contracts.
The linked prototypes were checked on an earlier baseline; this revision has
not been used to recompile them. Implementation acceptance uses current formulas.

## Required source behavior

A shared agreement contract compares the observations that a query source makes
of current and optional initial databases. Current table sources compare the full
optional table lookup. Initial sources compare the lookup through the optional
initial database. Pragmas compare their optional rows result. JSON and derived
sources impose no additional database premise under the common evaluation
context and intermediate source rows.

Table absence and shape are retained. Pragma agreement includes unsupported
results and database-dependent rows; it does not assert that all pragmas are
constant. The sufficient contract may compare table metadata unused by a query.
Minimal read footprints are outside this work.

One join argument, one source-fold induction and one subquery-depth induction
provide the source, correlated source, subquery run and context equalities.
Query `runOn` and `possibleOn` follow through this chain. Current and initial
origin tests supply short adapters, without their own evaluator inductions.

Replace the fourteen mirrored helper stages in `TwoStateReads` and
`TwoStateCurrentLaws`, identified in the findings. Preserve the two
statement-context formulas and the three downstream query formulas in
`TwoStateStatementLaws` under their original assumptions. Useful independent
source/read predicates remain available, owned below their proof consumers.
The new agreement API also admits simultaneous changes to both databases when
the selected observations agree, including fixed-pragma cases excluded by the
older syntactic read flags.

## Required expression behavior

A single mutual expression/argument induction proves equality of evaluation
value, fault and JSON subtype under agreement on allowed primitive node reads.
It uses the existing expression traversal and can constrain nodes with a mask.
It need not calculate a minimum set of reads. Different evaluation contexts and
rows can agree even when their complete records differ.

Primitive observations include column positions, parameters, counters, clock,
aggregates and the relevant subquery projection. Existence uses emptiness and
fault; scalar use uses the first value and first-row-certainty-sensitive fault;
membership uses first-column values and row-set-certainty-sensitive fault.
These cannot be merged into one certainty flag. Date functions may conservatively
require equal clocks. JSON subtype and lazy scalar operand behavior are retained.

The common proof derives the old `evaluate_append` and `Rowwise.evaluate_congr`
formulas. It derives stronger `evaluate_withSubqueries` and
`evaluate_certainFirst` formulas, preserving subtype and dropping their old
no-fallible-call exclusion. Other exclusions, including scalar subqueries where
required by certain-first replacement, remain. A caller may still need a
fallible-call restriction for admission or a different theorem.

A read-locality specialization permits local arithmetic, casts, JSON and scalar
calls when rows and parameters agree. Existing Rowwise expressions satisfy it
through a syntax adapter. `Rowwise.fault_none` and `Rowwise.calm` retain separate
proofs and their narrower hypotheses. Locality does not imply either claim.

Delete the replaced equality inductions and obsolete wrappers after migration.
Keep useful read adapters and semantic simplification facts with real consumers.
This is a congruence refactor, not an expression transformation framework or a
change to accepted SQL syntax. The new `Expr.evaluate_dropColumn` theorem in
`Resolution/ColumnDropExprLaws` changes the expression as well as the row.
Retain that distinct transformation theorem and its `RowFree` dependency;
the fixed-expression prototype does not subsume it, so it is not a fifth
required congruence replacement.

## Boundaries that matter

The source implementation puts `Query.readsInitial` and `Query.readsCurrent`
in `Resolution/QueryForm`, below `SourceAgreement`. Its shared core imports
`Execution` and `PossibleResults` and does not import the replaced endpoints.
`ExprAppendLaws` owns `EvalContext.RowFree` and
`ExprContextLaws` owns `SubqueryRun.certainFirst`. Put these definitions below
the shared proofs that use them. The experimental source core imports
`Execution` and `PossibleResults`; the expression core imports `ExprEval` and
`Resolution.ExprAny`. They do not call the endpoints they replace.

Actual expression consumers include `Expr.eval_append`,
`Connection.queryContext_selectOne`, `Connection.queryContext_selectOne_rows`
and `Query.simple_results_congr`. `SimpleQueryAppend` now shares its argument
through `Query.simple_results_agree` and `Query.filterKeeps_append`, with
`simple_results_append` as a specialization. Preserve that completed work,
the `_agree`/`_append` output laws in `CertifiedQueryOutputs`, and the
surface read-certificate proofs. `DerivedColumnRows` and `DerivedLookupRows`
also consume `Expr.eval_append`; preserve their general derived-expression
contracts. Preserve all these guarantees while migrating
their use of congruence. Source consumers in `TwoStateStatementLaws` feed later
statement/output laws. Import moves must compile those consumers too.
Read-certificate preservation now supports separate obligations at each branch's
reached connection and permits different table positions. Do not reintroduce
a common-connection premise when migrating these clients.

## Acceptance checks

- Recover every removed source helper formula and all five nominated context/
  query endpoints as temporary kernel-checked migration witnesses with original
  assumptions from `3e2212ed6983`. The two context formulas are among the fourteen
  helpers, so there are seventeen distinct source formulas. Universal proofs
  cover subquery depth and correlated traversal;
  this does not require a separate example at each depth or helper stage.
- Keep examples for absent versus present tables, unequal shape, a fixed
  pragma independent of both databases, and a database-dependent pragma.
  Equal row lists alone must not silently imply the full source contract.
- Recover the four nominated expression equality formulas, and kernel-check
  the two strengthened context-replacement formulas. Include a fallible local
  JSON call which the old hypothesis excluded.
- Keep regressions for scalar first certainty, membership rows certainty,
  lazy scalar arguments and JSON subtype. Equal value/fault pairs alone must
  not be treated as subtype equality. Include a local expression that is not
  Rowwise and one that can fault.
- Compile all actual consumers and checked public documentation. Audit standard
  axioms of generic proofs and independent instances without duplicate projection
  audits; inspect simp/instance/export uses before deleting names.
- Report the combined cost of the common proof, masks, adapters, caller changes
  and formula tests. Historical prototypes establish shared reasoning and
  stronger contracts at their recorded baseline; they do not establish current
  compilation, net source savings or compilation-time savings.

Use existing proof-test and Nix infrastructure with explicit timeouts. Execution,
conformance inputs and judge claims remain unchanged. No additional traversal
generator or testing framework is needed.

## Test lifetime

The fourteen old source-helper checks, old endpoint adapters and four old
expression-formula witnesses are migration evidence under ADR 0026. After
final Nix acceptance, retire redundant copies covered by current contracts
and migrated clients. Preserve the accepted historical revision for replay.

Keep focused checks of premise strength and meaning: source absence/shape and
pragma dependence; value, fault and JSON subtype; distinct certainty flags; and
the newly permitted fixed-pragma and fallible-local-expression cases. Reuse
existing examples first. A case that uniquely protects a requirement remains
until a consumer or focused regression covers it. The two stronger context laws
are current guarantees, not old-API compatibility obligations. Source counts,
old-name searches and dependency comparisons are one-time acceptance checks.
Record retirement in the existing status file; use existing test infrastructure.

## Assignment and coordination

Source and expression work can be assigned independently. Their import ownership
must agree with the foundational specification. Generalized congruence may
simplify query output work, but the query prototype does not depend on this
migration. Create dated task/status files only at assignment, using the then
current formulas and consumers as the migration inventory.
