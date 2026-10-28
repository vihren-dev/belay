# Source and expression agreement targets

Date: 2026-10-27. Status (2026-10-28): D2 and D5 implemented; final acceptance pending.
Audience: designers and reviewers.
Scope: [ADR 0026 D2 and D5][adr] and [agreement specification][spec].
Production baseline reviewed 2026-10-28: `3e2212ed6983`. Reconcile this inventory with the
implementation branch before editing. Prototype names do not prescribe the
production API. This is the target list, not a prescribed implementation order.
The fourteen source helpers and four required expression replacements are unchanged from
`3fe5caef`; the earlier prototype build is historical evidence, not validation
of its imports on latest main. Newly listed DROP COLUMN and derived-column
consumers are retained evidence, not additional replacement targets.

## One traversal for both database origins

The fourteen baseline declarations below are in namespace
`Belay.Sqlite.Model.Resolved`. [SourceAgreement.lean][agreement] replaces their
duplicated reasoning with one join argument, one fold induction and one
induction on arbitrary subquery depth. The old-owner links preserve the reviewed
baseline inventory; the two old production modules have been removed.
[The assigned task status](../plans/20261028-source-agreement.status.md) records
acceptance and temporary-witness retirement.

| File | Exact declarations |
| --- | --- |
| [TwoStateReads.lean][reads] | `QuerySource.join_initial_irrelevant`; `foldlM_join_initial_irrelevant`; `Query.source_initial_irrelevant`; `Query.sourceAfter_initial_irrelevant`; `Query.subqueryRun_initial_irrelevant`; `subqueryContext_initial_irrelevant`; `statementContext_initial_irrelevant` |
| [TwoStateCurrentLaws.lean][current] | `QuerySource.join_current_irrelevant`; `foldlM_join_current_irrelevant`; `Query.source_current_irrelevant`; `Query.sourceAfter_current_irrelevant`; `Query.subqueryRun_current_irrelevant`; `subqueryContext_current_irrelevant`; `statementContext_current_irrelevant` |

Agreement compares complete optional table lookups for each origin and the
optional result of `PragmaRows.rowsOn` for pragmas. Preserve missing tables,
table shape, unsupported pragma results and database-dependent pragma rows.
JSON and derived sources use the common evaluation context and intermediate
rows. Minimal read footprints and changes to executable source evaluation are
outside this work. Fixed pragmas can agree even when `readsCurrent = false`
does not hold.

The two statement-context formulas in the table remain derivable. The three
downstream query formulas in [TwoStateStatementLaws.lean][statement] also remain
derivable under their original assumptions, through the common argument:

- `Belay.Sqlite.Model.Resolved.Query.runOn_initial_irrelevant`.
- `Belay.Sqlite.Model.Resolved.Query.possibleOn_initial_irrelevant`.
- `Belay.Sqlite.Model.Resolved.Query.possibleOn_current_irrelevant`.

The fourteen old helper names are replacement targets. Preserve downstream
guarantees while migrating their proofs; this inventory does not order deletion
of every declaration whose name ends in `irrelevant`.

## One expression congruence induction

These four declarations are in namespace `Belay.Sqlite.Model.Resolved`.
Their common theorem must preserve the value/fault pair and JSON subtype,
including argument observations used by lazy scalar calls.

| File | Exact target | Required contract |
| --- | --- | --- |
| [ExprAppendLaws.lean][append] | `Expr.evaluate_append` | Recover its value/fault/subtype equality with its row-width, column-bound and `RowFree` assumptions. |
| [ExprContextLaws.lean][context] | `Expr.evaluate_withSubqueries` | Equal subquery runs at the evaluated row preserve value, fault and subtype; drop the old no-fallible-call premise. |
| [ExprContextLaws.lean][context] | `Expr.evaluate_certainFirst` | Preserve value, fault and subtype without the old no-fallible-call premise; retain the scalar-subquery exclusion. |
| [RowwiseExpr.lean][rowwise] | `Expr.Rowwise.evaluate_congr` | Recover equality from the same row and equal parameters through a read-locality adapter. |

`Expr.eval_append` in [ExprAppendLaws.lean][append] is the value projection and
an actual consumer, not a fifth expression induction. Migrate its proof and
callers with the same assumptions; keep a useful projection if consumers need it.

Primitive reads include columns, parameters, counters, clock, aggregates and
the relevant subquery observation. Existence reads emptiness and fault; scalar
use reads the first value and first-row certainty; membership reads first-column
values and row-set certainty. Preserve those distinctions. Equal clocks for all
date calls are an acceptable sufficient premise.

The two context laws will give the same equalities under weaker assumptions.
This does not remove admission or fault-freedom conditions elsewhere.
A row/parameter-local specialization can include arithmetic, casts, JSON and
scalar calls without claiming that all those expressions are fault-free.

## Definitions to put below their proof consumers

Names below have the prefix `Belay.Sqlite.Model.Resolved`.

| Current owner | Exact declarations | Disposition |
| --- | --- | --- |
| [Resolution/QueryForm.lean][queryform] | `Query.readsInitial`; `Query.readsCurrent` | Moved below the source agreement/origin adapters; meanings unchanged. |
| [EvalContextLaws.lean][evalcontext] | `EvalContext.RowFree` | Moved below its congruence adapter; meaning unchanged. |
| [EvalContextLaws.lean][evalcontext] | `EvalContext.plain_rowFree` | Plain-context evidence remains with the predicate. |
| [EvalContextLaws.lean][evalcontext] | `SubqueryRun.certainFirst` | Moved below the certainty adapter; record update unchanged. |

`Source.isInitial` and `Source.readsCurrent` already live in
[Resolution/QueryForm.lean][queryform]. Retain them there unless another concrete
ownership requirement arises. `Resolved.Statement.readsInitial` and
`Resolved.Statement.readsInitial_query` in [TwoStateStatementLaws.lean][statement]
remain useful statement-level classification facts; they are not duplicated
source traversals. Choose existing domain owners for moves, not a new global
utility layer. Do not copy definitions to break an import cycle.

## Downstream proofs to migrate and distinct facts to retain

The declarations in this section use the prefix `Belay.Sqlite.Model` unless a
different full namespace is stated. These are consumers and retained facts,
not an extra deletion inventory.

| File | Exact declarations affected by the new proof boundary |
| --- | --- |
| [TwoStateStatementLaws.lean][statement] | `runStatement_initial_irrelevant`; `SqlState.statementRun_initial_irrelevant`; `possibleOutput_initial_irrelevant`; `Output.ofStep_initial_irrelevant`; `resolvedStepOutput_initial_irrelevant` |
| [TwoStateQuery.lean][twostate] | `observeTwoState_initial_irrelevant` uses the output independence law. |
| [SelectOneSubqueryOutput.lean][selectone] | `Connection.queryContext_selectOne` uses subquery-context replacement. |
| [SelectOneRowsOutput.lean][selectrows] | `Connection.queryContext_selectOne_rows` uses both strengthened context laws. |
| [TwoStateNotExistsExcept.lean][except] | `Resolved.Query.simple_results_congr` uses rowwise congruence. |
| [KeysUniqueAddColumn.lean][keys] | `LiteralData.termValue_append`; `LiteralData.keyEqual_append` use `Resolved.Expr.eval_append`. |
| [RowLocalAddColumnTheorems.lean][rowlocal] | `Table.ChecksHold.appendColumn` uses `Resolved.Expr.eval_append`. |
| [SimpleQueryAppend.lean][simpleappend] | `Resolved.Query.filterKeeps_append`, `.simple_results_agree`, `.simple_results_append`; retain the existing common proof and its specialization. |
| [CertifiedQueryOutputs.lean][certified] | `runScriptStep_simpleTable_output_agree`, `runScriptStep_simpleTable_output_append`; preserve distinct statements/filters and differing table positions where admitted by their formulas. |
| [ReadCertificatePreservation.lean][readcertificate] | `Belay.Sqlite.ReadCertificate.preservesAt` and `.preservesAt_send`; retain per-branch obligations without requiring all branches to reach one connection. |
| [DerivedColumnRows.lean][derivedrows] | `assign_derived_append`, `updated_derived_append` use the append congruence for general derived expressions. |
| [DerivedLookupRows.lean][derivedlookup] | `Resolved.Expr.eval_compare_stored_left`, `.eval_compare_stored_right` use `Expr.eval_append` for probes. |
| [Resolution/ColumnDropExprLaws.lean][drop-expr] | `Resolved.Expr.evaluate_dropColumn`, `.eval_dropColumn` consume `RowFree`; retain their separate expression-reindexing guarantees. |

Retain `Resolved.Expr.Rowwise`, `Resolved.Expr.Rowwise.fault_none` and
`Resolved.Expr.Rowwise.calm` in [RowwiseExpr.lean][rowwise], including their
distinct hypotheses. The same file's `Resolved.Value.and_cases`,
`Resolved.truthy_isNot_one_of_cases` and `Resolved.Expr.truthy_isNot_one_and`
are separate truth laws. Expression locality does not replace these facts.
`evaluate_dropColumn` changes the expression and is outside the four required
replacements; the fixed-expression prototype does not establish that stronger
abstraction. Moving `RowFree` must still compile this consumer and its CHECK/key
proof clients. Derived-column clients replace the removed `NormalizedField`
family; there is no old migration family to preserve as a compatibility API.

In [EvalContextLaws.lean][evalcontext], keep the useful `Resolved.EvalContext.withRuns`,
`Resolved.EvalContext.withRuns_subqueries`, `Resolved.EvalContext.withRuns_parameters`,
and the `Resolved.SubqueryRun.certainFirst_rows`, `Resolved.SubqueryRun.certainFirst_fault`,
`Resolved.SubqueryRun.certainFirst_rowsCertain`, `Resolved.SubqueryRun.certainFirst_firstCertain` projection laws with
their consumers and simp registrations. Their placement can follow moved
definitions. Their presence is not a reason to keep a duplicated induction.

## Tests and their lifetime

- [surface_two_state_test.py][twotest] contains a `PUBLIC_THEOREMS` axiom list
  with old source helper names. Migrate that list to meaningful current proofs;
  retain its native observation, changed-current-database and origin-swap checks.
- [surface_claims_test.py][claimtest] compiles real query clients, including
  [ClaimsExists.lean][existsfixture], [ClaimsIn.lean][infixture] and
  [ClaimsMayFail.lean][failfixture]. Retain their semantic guarantees and current
  API uses; dropping a congruence premise does not change SQL fault behavior.
- [surface_assertion_examples_test.py][asserttest] owns two-state assertion and
  purge-frame examples. Keep those applications, including the Rowwise evidence
  in [PurgeFrameQueries.lean][purgefixture] and the NULL/trigger distinctions.
- [surface_derived_column_test.py](../tests/surface_derived_column_test.py) covers
  current derived-column clients. Reuse it and existing DROP COLUMN conformance;
  this update does not require a separate per-expression migration matrix.
- During migration, kernel-check all removed helper formulas and nominated
  endpoint formulas with their `3e2212ed6983` assumptions. Retire redundant old/new
  equivalence matrices after Nix acceptance of the final contract-changing slice.
  Keep the accepted revision for replay, not a second maintained proof API.
- Keep focused current checks for absence/shape, pragma dependence, faults,
  JSON subtype and distinct certainty fields. Reuse real clients and existing
  examples first; retain a witness while it uniquely protects a requirement.
  Audit generic proofs and independent evidence without per-wrapper duplicates.

Update checked docs, exports and imports for changed names. Production
evaluators, accepted SQL, conformance inputs and judge claims remain unchanged.

[adr]: adr-0026-semantic-proof-boundaries.md
[spec]: spec-proof-agreement.md
[agreement]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/SourceAgreement.lean
[reads]: https://github.com/vihren-dev/sqlite-verifier/blob/3e2212ed6983f36144b7fc5bdce9b263f939e50f/packages/belay-sqlite-model/Belay/Sqlite/Model/TwoStateReads.lean
[current]: https://github.com/vihren-dev/sqlite-verifier/blob/3e2212ed6983f36144b7fc5bdce9b263f939e50f/packages/belay-sqlite-model/Belay/Sqlite/Model/TwoStateCurrentLaws.lean
[statement]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/TwoStateStatementLaws.lean
[append]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ExprAppendLaws.lean
[context]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ExprContextLaws.lean
[evalcontext]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/EvalContextLaws.lean
[rowwise]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowwiseExpr.lean
[queryform]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/QueryForm.lean
[twostate]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/TwoStateQuery.lean
[selectone]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/SelectOneSubqueryOutput.lean
[selectrows]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/SelectOneRowsOutput.lean
[except]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/TwoStateNotExistsExcept.lean
[keys]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/KeysUniqueAddColumn.lean
[rowlocal]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/RowLocalAddColumnTheorems.lean
[simpleappend]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/SimpleQueryAppend.lean
[certified]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/CertifiedQueryOutputs.lean
[readcertificate]: ../packages/belay/Belay/Sqlite/ReadCertificatePreservation.lean
[derivedrows]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/DerivedColumnRows.lean
[derivedlookup]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/DerivedLookupRows.lean
[drop-expr]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/ColumnDropExprLaws.lean
[twotest]: ../tests/surface_two_state_test.py
[claimtest]: ../tests/surface_claims_test.py
[asserttest]: ../tests/surface_assertion_examples_test.py
[existsfixture]: ../tests/surface/ClaimsExists.lean
[infixture]: ../tests/surface/ClaimsIn.lean
[failfixture]: ../tests/surface/ClaimsMayFail.lean
[purgefixture]: ../tests/surface/PurgeFrameQueries.lean
