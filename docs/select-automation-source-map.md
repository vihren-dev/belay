# SELECT proof automation: source map

Date: 2026-10-28. Source baseline: `3e2212ed`.
Audience: designers and reviewers. This inventory supports
[ADR 0027](adr-0027-compositional-select-proofs.md) and its
[acceptance contract](select-automation-acceptance.md).
It distinguishes existing model definitions and laws from proposed proof rules.
It makes no new claim about agreement with native SQLite.

## Resolved constructor inventory

[QueryForm][query-form] defines the query, sources and joins.
[ResolvedExprForm][expr-form] defines expressions, aggregates and output columns.
Surface CASE, aliases, USING, NATURAL, views and CTEs are resolved into these
forms; they are not additional constructors of `Resolved.Expr` or `Source`.

| Type or field | Existing cases | What a decomposition must retain |
| --- | --- | --- |
| `Source` | `table`, `initialTable`, `each`, `subquery`, `pragma` | Current/initial database origin; source fault; derived-query index and width; enclosing cells |
| `JoinKind` | `inner`, `left`, `right`, `full` | ON truth, duplicate matches and unmatched rows with NULL extension |
| Empty source list | SELECT without FROM | The initial source is one empty row, not no rows |
| `Expr`, data | `column`, `literal`, `parameter`, `aggregateValue` | Positional reads, missing-value defaults and group context |
| `Expr`, logic | `compare`, `and`, `or`, `not`, `isNull` | Affinity, collation, three-valued logic, value and fault |
| `Expr`, computation | `arithmetic`, `cast`, `coalesce`, `inList` | Modeled conversions, NULL behavior and evaluation demand |
| `Expr`, functions/context | `json`, `date`, `scalar`, `now`, `counter` | Existing function families, argument order, clock and known counters |
| `Expr`, nested queries | `exists`, `inQuery`, `subquery` | Outer-row dependence and the certainty condition of each consumer |
| `Arguments` | `nil`, `cons` | Argument values and faults in written order |
| `Aggregate`, counting/extrema | `countRows`, `count`, `min`, `max` | Empty and NULL inputs; extrema collations and representative values |
| `Aggregate`, numeric | `sum`, `avg`, `total` | Modeled summation, empty inputs and overflow |
| `Aggregate`, collection/text | `jsonGroupArray`, `jsonGroupObject`, `groupConcat` | Input order, JSON binary flag, labels and per-row separator |
| Resolved `Output` | `scalar`, `aggregate` | Scalar row or group-head evaluation; whole-group aggregate evaluation |
| `SortKey` | `expression`, `output` | Hidden sort values or output index; each term's direction/collation |
| `Query.distinct` | `none`, `some collations` | Per-column comparison and representative certainty; this is not a Boolean |
| Compound operators | `unionAll`, `union`, `intersect`, `except` | Left-to-right combination, multiplicity, collation and run ending |
| Window | Literal fields and optional parameter indexes | Binding, conversion failure, OFFSET/LIMIT order and permitted tie cuts |

`Query` also retains sources, filter, aggregate flag, grouping terms, columns,
names, order terms, outer width, indexed aggregates, HAVING and optional compound.
A compound stores its first term index, operator/index chain and collations.
The expression inventory above includes all 21 constructors; the aggregate
inventory includes all 10. Function families remain parameters of their rules:
coverage does not require automatic solution of every function-specific fact.

## Existing laws and required extensions

Names in this table are existing declarations. Required extensions describe the
general interfaces that ADR 0027 proposes; the table does not assert that no
special-case theorem elsewhere can help prove them.

| Phase | Existing reusable declarations | Required extension |
| --- | --- | --- |
| Source lookup | `Database.table_of_findTable`, `Query.source_first` in [TableSourceLaws][table-laws]; `Query.source_none` in [QueryJoinLaws][join-laws] | Collection specifications for every source constructor and the source fold |
| Joins | `sourceRows_width`, `joinMatches_width`, `joinRow_width`, `joinRows_width`, `joinRows_left_keeps`, `joinRows_right_keeps` in [QueryJoinLaws][join-laws] | Matched/unmatched collection rules retaining multiplicity and outer cells |
| Expressions | `Expr.eval_column`, `eval_parameter`, logic and nested-query equations in [ExprEvalLaws][expr-laws]; `Expr.evaluate_withSubqueries` in [ExprContextLaws][context-laws] | Value/fault rules for each constructor with explicit context premises |
| Filter | `mem_filtered` in [QueryLaws][query-laws] | Complete-collection and cardinality rules, beyond unary membership |
| Group | `groups_eq_fold`, `groups_short_iff_pairwise`, `groups_long_iff_repeated` in [GroupsPairwise][group-laws] | Partition, multiplicity and representative-row rules for arbitrary group predicates |
| Aggregate | `Query.aggregateOf_results`, `aggregateOf_fails`, `aggregateOf_run_of_faultless` in [AggregateQueryLaws][aggregate-laws] | Grouped, multi-output and aggregate-expression composition for every aggregate |
| Projection | `Query.Simple.results_eq` in [SimpleResultsLaws][simple-results] | Characterization of general `records`, including HAVING and hidden sort keys |
| DISTINCT/compound rows | `Resolved.mem_of_mem_distinctRows`, `CompoundOperator.except_combine_eq_nil` in [ExceptCombineLaws][except-laws] | Record DISTINCT and every compound operator, with certainty premises |
| Sort | `stableSort_perm`, `sort_perm`, `sort_sorted` in [QueryLaws][query-laws] | Transfer of collection predicates and observable ordering facts |
| Window | `Query.bindWindow_literal`, `bindWindow_some` in [QueryWindow][window]; `windowRows_sublist` in [PossibleResultsLemmas][possible-lemmas] | Parameter/error and tie-boundary rules, not only a representative list slice |
| Alternatives | `Query.normalResult_mem`, `possibleResults_ne_nil`, `possibleResults_length` in [PossibleResultsLaws][possible-laws] | Transfer of arbitrary predicates to every permitted result |
| Output construction | `Output.ofResults_listed`, `Output.listed_iff` in [OutputResultsLaws][output-laws] | Successful-result predicates and their nonempty-alternative bridges |
| Execution | `resolvedStepOutput_query` and `Query.described` in [QueryStatementOutput][statement-output]; `Sql.check_query_select` in [ReadStepRule][read-rule] | General phase-to-execution adapters retaining actual readiness and context |

The pure pipeline already exists: [QueryEval][query-eval] supplies filtering,
grouping, aggregates and sorting; [QueryResults][query-results] supplies records,
DISTINCT and results. [QueryRun][query-run] supplies faults and window binding.
New characterization lemmas can expose fused phases without replacing evaluators.

## Conditions that rules must preserve

- Table presence is distinct from row width and column constraints.
  `Query.source_first` sets a width field but does not prove `Table.RowsWide`.
  Missing positional cells can read NULL. Outer joins can add NULL even for a
  source column constrained NOT NULL. See [QueryJoins][joins].
- Without GROUP BY, aggregation has one group even on empty input. Explicit
  GROUP BY can have zero groups. Grouped scalars and HAVING read `group.headD []`
  under `Query.groupContext`. Collation-equivalent keys need not be equal raw
  values; no raw-equality or permutation-invariance premise follows from that
  equivalence alone. See [QueryResults][query-results].
- `distinctCertain` requires SQL-equal output rows to be identical values.
  [CompoundRows][compound-rows] has corresponding `keepsCertain` checks.
  Uncertain representatives become `.may`; pure chosen rows do not certify
  a successful statement.
- [Subqueries][subqueries] distinguishes first-cell certainty, first-column
  multiset certainty and complete-row multiset certainty. Scalar, IN and FROM
  consumers use different conditions. A derived source also needs no fault and
  `RunEnd.done`. `EvalContext.Quiet` omits complete-row certainty and the ending.
  The outer prefix is padded/truncated to `Query.outer`; it is not sibling data.
- [CompoundRun][compound-run] retains operator-specific execution demand.
  A full UNION ALL limit skips later terms; empty left EXCEPT/INTERSECT operands
  can skip the right term. Window conversion and failures after earlier rows
  affect the ending. Requiring every operand to succeed is only a sufficient rule.
- [QueryOutputCases][output-cases] provides `Query.outputOn_clean` with only
  `run.fault ≠ .must`; this permits `.may`. Execution also needs statement
  readiness, including plain nested subqueries and no `.may` source/run faults.
  Missing source rows and missing bound windows require their actual branches.
- [PossibleResults][possible] normalizes tie groups and enumerates window
  choices. The normal representative belongs to the alternatives, and all have
  its length. Neither fact transfers arbitrary collection predicates by itself.
  These observations do not enumerate every physical row permutation.
- [OutputChoice][choices] includes the raw `.oneOf` wrapper and each concrete
  `.rows` choice. Their reached traces differ. [Run][run] stores one actual
  execution and omits parts of the full execution context. Its observation
  predicate cannot certify arbitrary output-dependent program continuations.

Resolver restrictions remain separate from proof-search limits. Examples are
bare aggregate columns, fallible calls consuming aggregate values, unsupported
GROUP BY expressions and grouped SUM with a window. See
[QueryBodyTraced][query-body], [QueryTerms][query-terms] and the
[supported subset](semantic-subset.md). Rule coverage must retain those branches;
it does not add SQL syntax or turn an unsupported observation into successful rows.

[query-form]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/QueryForm.lean
[expr-form]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/ResolvedExprForm.lean
[table-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/TableSourceLaws.lean
[join-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryJoinLaws.lean
[expr-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ExprEvalLaws.lean
[context-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ExprContextLaws.lean
[query-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryLaws.lean
[group-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/GroupsPairwise.lean
[aggregate-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/AggregateQueryLaws.lean
[simple-results]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/SimpleResultsLaws.lean
[except-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/ExceptCombineLaws.lean
[window]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryWindow.lean
[possible-lemmas]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/PossibleResultsLemmas.lean
[possible-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/PossibleResultsLaws.lean
[output-laws]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/OutputResultsLaws.lean
[statement-output]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryStatementOutput.lean
[read-rule]: ../packages/belay/Belay/Sqlite/ReadStepRule.lean
[query-eval]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryEval.lean
[query-results]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryResults.lean
[query-run]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryRun.lean
[joins]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryJoins.lean
[compound-rows]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/CompoundRows.lean
[subqueries]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Subqueries.lean
[compound-run]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/CompoundRun.lean
[output-cases]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryOutputCases.lean
[possible]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/PossibleResults.lean
[choices]: ../packages/belay/Belay/Sqlite/ExecutionBranches.lean
[run]: ../packages/belay/Belay/Sqlite/ProgramRun.lean
[query-body]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/QueryBodyTraced.lean
[query-terms]: ../packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/QueryTerms.lean
