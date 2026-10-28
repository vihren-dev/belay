# Source agreement and expression congruence experiments

Created 2026-10-26. Production source is unchanged. The experiment uses the model
artifacts recorded in the theorem-dependency report for revision `3fe5caef`.

## Decisions

- **Adopt source agreement.** There are two copies of the same join/fold/nesting
  argument. One contract proves both existing origin-irrelevance endpoints and
  also supports changes to both databases when the selected observations agree.
- **Narrow expression work to congruence.** A shared induction does work for all
  four nominated equality laws, including JSON subtype, faults and the different
  subquery certainty fields. It does not subsume fault-freedom or syntactic
  calmness. Do not promise fewer total lines or replace the entire Rowwise API.

## Source result and inventory

`SourceAgreement.lean` defines agreement on the database observations of a source:

- Current table: equality of `Database.table position : Option Table`.
- Initial table: equality of the optional initial database's table lookup.
- Pragma: equality of `PragmaRows.rowsOn database : Option (List (List Value))`.
- JSON and derived sources: no extra database premise; the shared context and
  intermediate source rows determine their behavior.

The table condition deliberately retains absence and complete shape, including
the width used by outer joins. It is sufficient rather than minimal: it also
requires equal table metadata that a particular query may never inspect. The
pragma condition preserves unsupported results and database-dependent check
rows. It is not a claim that all pragmas have fixed rows.

The proof contains one join case split, one optional fold induction and one
induction on arbitrary subquery depth. `source`, correlated `sourceAfter`, the
complete `subqueryRun`, statement contexts, `runOn` and `possibleOn` are derived
from those arguments. No specialized irrelevance theorem is used.

The existing replacement candidates are exactly these seven paired stages:

| Stage | Initial file/line | Current file/line |
|---|---|---|
| `QuerySource.join_*_irrelevant` | `TwoStateReads.lean:29` | `TwoStateCurrentLaws.lean:18` |
| `foldlM_join_*_irrelevant` | `TwoStateReads.lean:39` | `TwoStateCurrentLaws.lean:28` |
| `Query.source_*_irrelevant` | `TwoStateReads.lean:54` | `TwoStateCurrentLaws.lean:42` |
| `Query.sourceAfter_*_irrelevant` | `TwoStateReads.lean:61` | `TwoStateCurrentLaws.lean:49` |
| `Query.subqueryRun_*_irrelevant` | `TwoStateReads.lean:70` | `TwoStateCurrentLaws.lean:58` |
| `subqueryContext_*_irrelevant` | `TwoStateReads.lean:81` | `TwoStateCurrentLaws.lean:68` |
| `statementContext_*_irrelevant` | `TwoStateReads.lean:103` | `TwoStateCurrentLaws.lean:90` |

Paths in the table are under `packages/belay-sqlite-model/Belay/Sqlite/Model/`.
The graph and a source search agree that this helper family serves only its
own chain and the three query endpoints in `TwoStateStatementLaws.lean:34`,
`:48`, and `:62`. Keep those endpoint formulas during migration; their later
statement/output clients need no new assumptions. Retaining all fourteen old
intermediate helpers as permanent wrappers would defeat the intended reduction.

`SourceEndpoints.lean` derives both existing statement-context formulas, both
existing permitted-result formulas, and the existing initial-origin full-run
formula. The current and initial source tests are small adapters to agreement,
not separate evaluator inductions. `SourceChecks.lean` checks that missing and
present tables disagree, shape is retained, and a fixed-pragma query is independent
of both databases despite failing the old `readsCurrent = false` test.

The core imports `Execution` and `PossibleResults`, below the specialized laws.
The endpoint experiment imports `TwoStateReads` because it currently owns
`Query.readsInitial` and `Query.readsCurrent`; place those predicates below the
new laws during implementation. No production import cycle was introduced.

## Expression result and limits

`ExpressionAgreement.lean` proves one theorem over primitive node observations
and the existing `Expr.any` traversal. It has one mutual expression/argument
induction. Both value/fault equality and JSON-subtype equality are conclusions.
The argument induction retains individual head/tail evaluations for lazy `iif`,
and argument values for `json_extract`'s dynamic subtype.

Subqueries have three distinct observations: existence reads emptiness and fault;
scalar use reads the first value and its certainty-sensitive fault; membership
reads first-column values and its row-set-certainty-sensitive fault. There is no
blanket equality on the whole subquery run. Clock, aggregates, parameters,
counters and column positions also have explicit observations. Date calls
conservatively require equal clocks even when a particular call ignores them.

| Existing candidate | Result | Actual compiled direct consumers |
|---|---|---|
| `ExprAppendLaws.lean:33`, `Expr.evaluate_append` | Exact value/fault/subtype formula recovered | `Expr.eval_append` |
| `ExprContextLaws.lean:36`, `Expr.evaluate_withSubqueries` | Stronger: subtype equality; no fallible-call exclusion | `Connection.queryContext_selectOne`, `Connection.queryContext_selectOne_rows` |
| `ExprContextLaws.lean:77`, `Expr.evaluate_certainFirst` | Stronger: subtype equality; no fallible-call exclusion; scalar-subquery exclusion retained | `Connection.queryContext_selectOne_rows` |
| `RowwiseExpr.lean:44`, `Expr.Rowwise.evaluate_congr` | Exact formula recovered through a syntax-only adapter | `Query.simple_results_congr` |

The stronger context statements are proved, not inferred from unchanged tests.
The old no-fallible-call premises are unnecessary for these equalities because
the new proof preserves argument subtype and the complete fault calculation.
Other admission conditions in their callers may still need those premises;
this experiment does not remove them from caller contracts or SQL scope checks.

`ExpressionRowwise.lean` additionally proves context independence for every
expression whose reads are confined to its row and parameters. This admits
arithmetic, casts, JSON and scalar calls excluded by the existing Rowwise
whitelist. A small induction proves existing Rowwise expressions meet the read
boundary. Keep `Rowwise.fault_none` and `Rowwise.calm` separate: arbitrary local
JSON/scalar calls can fail, so locality does not imply either property.

`ExpressionChecks.lean` kernel-checks that scalar certainty changes fault,
membership uses a different certainty field, and equal value/fault pairs can
have different JSON subtypes. It also instantiates the strengthened theorem on
a fallible JSON expression and proves a JSON expression local but not Rowwise.

The generic expression core is 112 lines, its three endpoint adapters 68 lines,
and its broader locality result/Rowwise adapter 46 lines, including documentation
and axiom reports. This is evidence of shared reasoning and broader contracts,
not measured net code shrinkage. There are four equality proof inductions to
consolidate, but the mask adapters and syntax certificate still have a cost.
Do not generalize this into arbitrary expression transformations or a universal
semantics framework without another concrete consumer.

The core imports only `ExprEval` and `Resolution.ExprAny`. Endpoint imports of
specialized files supply the existing `EvalContext.RowFree` and
`SubqueryRun.certainFirst` definitions, not their equality theorems. Move these
definitions below the specialized laws if their new consumers require it.

## Validation and caveats

The pinned Lean 4.34.1 compiler compiled all seven files without warnings, with
a 120-second timeout per file. Compile order is `SourceAgreement`,
`SourceEndpoints`, `SourceChecks`, `ExpressionAgreement`, `ExpressionEndpoints`,
`ExpressionRowwise`, `ExpressionChecks`. Every printed axiom list is a subset
of `propext`, `Classical.choice`, and `Quot.sound`; no sorry or native oracle is
used. The standalone Nix experiment target is the final reproducible check.

Graph counts describe direct stored-expression references in the selected
report, including compiler-generated helpers when present. They are not a
proof of source non-use or public dead code; source searches supplied the
additional evidence above. No build-time or proof-cost improvement was measured.
