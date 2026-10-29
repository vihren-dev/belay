# SELECT proof automation: acceptance contract

Date: 2026-10-28. Status: DRAFT; proposed behavior, not current functionality.
Audience: designers and reviewers. Governing proposal:
[ADR 0027](adr-0027-compositional-select-proofs.md).

## Meaning of completion

Semantic rules cover each existing modeled SELECT phase. Automation closes the
positive cases below using stated hypotheses and supporting lemmas, without a
hint proving the complete target query. Negative cases check exact refusals or
prove the neighboring counterexample; timeout alone is not evidence of rejection.
Residual cases check the actual goals and recovery behavior, not only a failure
message. All closed proofs use the existing allowed axiom/dependency policy.

Use symbolic database contents for schema-based theorems. Concrete examples
check boundary semantics but cannot replace those universal proofs. Give each
schema premise an empty and populated valid witness where applicable. An
inconsistent premise must not be the only way a positive theorem can hold.
Use the existing surface/Nix test harness, proof-axiom checks and finite budgets.
Implementation acceptance is separate from the feasibility experiments.

## Public claims and automation

For each applicable case, prove a standard `Sql.check` claim at an explicit
context. Exercise successful-result and row-wise conveniences on representative
cases and prove their connection to the general claim. A returned error can
satisfy an explicitly error-accepting post; it cannot satisfy a successful-result
claim. A predicate on a `Run` observation is not automatically equivalent to a
context-sensitive program triple.

The motivating theorem has arbitrary valid `db`, a supplied invoices catalog
fact, and the literal query `SELECT customer FROM invoices WHERE id=1`.
It concludes successful rows with a present non-NULL first cell. Proposed proof:
`by sql_auto [schema]`. The theorem does not assume invoice 1 exists, TEXT values
are the only possible values, or that stored data equals a concrete example.
Also prove it with generic table/column-presence premises rather than exact
catalog equality, to keep the public rule applicable to other catalogs.

For a script `s` with exactly one syntactic SELECT, a proof
`one : s.statements.length = 1`, fixed `db` and `env`, and context-independent `Q`,
the proposed successful-result bridge is:

```lean
(db.run (query s one) env).returnsResult Q ↔
  (query s one).check (fun result _ => match result with
    | .ok rows => Q rows | .error _ => False) (ExecutionContext.initial db env)
```

The implementation proves the nonemptiness of generated alternatives. A `send`
bridge has its own statement; this equivalence does not cover arbitrary programs.
`returnsRows P` specializes `Q` to `fun rows => ∀ row ∈ rows, P row`.
`sql_select` introduces leading universal binders and implications and handles
these conveniences, `Q (query.results context rows)`, universal predicates over
`query.possibleResults context rows`, and `Q (phase arguments)` for the phase
functions in the [source map](select-automation-source-map.md). `sql_run` handles
`Sql.check` and triples and delegates their SELECT obligations to that procedure.

## Automatic acceptance matrix

Each positive entry is required at feature completion. Listed assumptions are
examples of the relevant facts; fixtures must state their exact formal versions.

| ID | Query family and positive property | Required contrast |
| --- | --- | --- |
| A01 | NOT NULL projection on arbitrary valid tables; width and cell existence | Empty result allowed; nullable source cannot establish non-nullness |
| A02 | `WHERE x IS NOT NULL` establishes non-nullness without a schema constraint | CHECK that accepts NULL is insufficient without the filter |
| A03 | `WHERE amount > :minimum` establishes the modeled comparison for every output | NULL, affinity and parameter type cases; no unproved host numeric interpretation |
| A04 | Plain projection preserves source length and duplicates; filtering bounds length | A row-wise property does not imply cardinality or distinctness |
| A05 | Inner join produces matching concatenated rows; a supplied unique/existing match gives a cardinality theorem | Multiple matches multiply rows; missing match can remove rows |
| A06 | LEFT, RIGHT and FULL join facts identify matched versus NULL-extended rows | Non-nullness on the optional side is not inferred from its table constraint |
| A07 | GROUP BY gives a partition with modeled key equivalence, multiplicity and nonempty groups | Raw Value equality does not follow from collated key equality |
| A08 | COUNT(*) without GROUP BY is one output row, including zero on empty input; grouped empty input returns no groups | Empty source does not imply empty aggregate output |
| A09 | COUNT(x)=COUNT(*) under a non-NULL premise; SUM/MIN/MAX empty and NULL cases | SUM needs an overflow premise; MIN/MAX use modeled comparison |
| A10 | HAVING keeps exactly groups with a true condition, including COUNT-based conditions | NULL HAVING does not retain a group |
| A11 | Scalar projection combines copied columns, parameters and a modeled arithmetic/CASE expression | Expression value alone does not discharge its failure obligation |
| A12 | DISTINCT establishes uniqueness under its actual collations and preserves a suitable row property | Different but SQL-equal representations do not imply raw equality or a fixed representative |
| A13 | ORDER BY establishes modeled ordering and preserves cardinality and row properties | Sort expressions need not occur in SELECT outputs |
| A14 | LIMIT/OFFSET establishes size bounds and properties of every possible selected row | Tied winners need not be identical; test zero, one, many and offset past end |
| A15 | Parameterized LIMIT/OFFSET with valid bounds; invalid binding has an explicit error post | Binding error is not empty successful output; demand-sensitive LIMIT 0 behavior retained |
| A16 | UNION ALL adds multiplicities; UNION, INTERSECT and EXCEPT prove their modeled membership properties | No conversion of bags to sets before an operator permits it |
| A17 | Derived SELECT and a modeled view/nonrecursive CTE reuse an inner collection specification | Inner output columns need not retain source constraints; source certainty required |
| A18 | Correlated EXISTS returns only rows with a matching witness, with two different outer rows | A subquery proof for one outer row cannot serve every row |
| A19 | Scalar and IN subquery observations use their respective first-value and first-column rules | Empty scalar result yields NULL; IN/NOT IN include NULL semantics |
| A20 | No-FROM SELECT, pragma rows and supported json_each sources each have a source-rule example | No-FROM starts with one empty row; json_each faults are not silently removed |
| A21 | Read after a preceding statement uses its reached database and full execution context | Initial-state facts cannot be reused after a relevant update without proof |
| A22 | Context-dependent read has explicit clock/counter premises and a context-preserving result proof | Default-environment proof is not generalized to every environment automatically |

A09 must also exercise at least one non-count aggregate family beyond SUM/MIN/MAX
through its generic rule, such as GROUP_CONCAT or a JSON aggregate. All remaining
aggregate and expression constructors require semantic rules and a checked
decomposition test even where automatic closure needs a user lemma. This permits
specialized arithmetic solvers without silently excluding model constructors.

## Semantic coverage inventory

The implementation supplies a source-linked table of rule declarations and
checked applications for these domains. A function that merely unfolds the
entire execution engine is not a phase rule.

- Sources: current and initial tables, no source, pragma, json_each, indexed
  derived queries; all join kinds and resolved USING/NATURAL behavior.
- Expressions: every constructor of `Resolved.Expr`; aggregate references,
  parameters, affinities, collations, arithmetic and scalar calls, JSON/date,
  clock/counters, CASE/coalesce and subquery observations retain value and fault
  semantics. Missing indexes and parameters cannot invent cell-existence facts.
- Groups and aggregates: all constructors of `Aggregate`, including COUNT,
  MIN/MAX, SUM/AVG/TOTAL, GROUP_CONCAT and JSON groups; representative group rows,
  aggregate references, empty groups, faults and order-sensitive results.
- Results: projection records, distinct records, compound combinations, sorting,
  parameter binding, slicing, tie alternatives and output normalization.
- Execution: source acquisition, model readiness, expression/source faults,
  overflow, mismatch, raw/concrete OutputChoice and full context transitions.

Resolution's unsupported forms stay unsupported: examples include window
functions, aggregate DISTINCT/FILTER forms absent from the AST, rejected bare
aggregate columns, unsupported grouping expressions and grouped SUM with a
window. The versioned inventory uses current source definitions rather than an
open-ended promise about future model constructors. Adding a model constructor
later requires updating its rule coverage explicitly.

## Error, residual and trust acceptance

Proposed extension syntax (not yet implemented):

```lean
attribute [local sql_select_rule filter] my_filter_rule
-- A proved rule about filtering, not a proof of the whole query:
-- ∀ rows, AllRows P rows → AllRows Q (rows.filter test)
example ... := by sql_select [my_filter_rule, schema_fact]
```

The attribute accepts one phase. Explicit hints run in supplied order, then
registered rules run in qualified declaration-name order; there is no priority option.
Supported phase names are `source`, `expression`, `filter`, `group`, `aggregate`,
`having`, `project`, `distinct`, `order`, `window`, `compound`, `subquery` and
`execution`. Here, `window` means LIMIT/OFFSET and tie-boundary selection;
SQL window functions using OVER remain unsupported. The example's AllRows is the ordinary universal membership
predicate, not a required new public type. Registration accepts proved theorem
declarations. The phase is a routing tag; ordinary Lean theorem application matches
the conclusion to the current goal and retains all premises as goals. Reject
non-theorem declarations; skip inapplicable proved rules without changing the goal.
Built-in and imported rule libraries use this same registry. Local registration
ends with its section; ordinary global registration persists through imports,
so a library can supply reusable rules. Namespace names alone do not create local registration.
No scoped-namespace activation mechanism is required in addition to local/global
registration. Direct hints can supply applicable lemmas without registration.

Test an unrelated registered rule, a rule with an unresolved premise, and local
registration outside its scope. These cases distinguish useful extensibility
from unbounded rewriting or accidental global changes.

| ID | Required behavior |
| --- | --- |
| B01 | Modeled error fails successful-result claims but can satisfy an explicit matching error post. Unmodeled stop fails Sql.check even with post True. |
| B02 | All alternatives satisfy the post; one bad alternative prevents a success proof. Nonempty alternatives are required. Raw oneOf and concrete choices preserve their different traces. |
| B03 | A supplied false precondition can prove a triple logically, but it cannot stand in for the nonvacuous A01 theorem. False goals with valid witnesses cannot close. |
| B04 | Unknown shape or unsolved user arithmetic leaves the exact relevant typed premise under the correct assumptions. Model restriction and solver incompleteness are distinguishable. |
| B05 | A query with a `.may` fault cannot gain successful-execution certification solely through Query.outputOn_clean. Source and statement readiness remain required. |
| B06 | Budget exhaustion and cancellation restore the original sql_auto goal and siblings; no hidden sorry or changed claim. Nested searches do not reset budgets. |
| B07 | Generated replacement proof elaborates independently with ordinary allowed axioms. A deliberately invalid supplied rule cannot create a kernel-accepted proof. |
| B08 | A user-supplied proved rule discharges a phase outside built-in automatic closure. Manual composition remains possible without tactic registration. |
| B09 | Rule choice is deterministic; cyclic registrations terminate within budget. Hints cannot discard premises or assume the target. |
| B10 | Background checking recognizes the new goal shapes, preserves dependency exclusions, and emits no success on unknown, cancelled or incomplete proofs. |
| B11 | SELECT preparation errors use the actual resolution error and can satisfy a matching error post, but cannot satisfy successful-result claims. |

Explicitly test skipped-work boundaries: LIMIT 0, empty compound operands and
short-circuiting expressions. Requiring every syntactic expression to succeed
can be a useful sufficient lemma, but is not the only general decomposition
route for model executions that skip those expressions.

## Performance and evidence

Retain the current public resource controls: standalone tactics use the caller's
Lean heartbeat and recursion limits; command checking uses `sql.checkBudget`
(currently 100000) and `sql.checkRecursionLimit` (currently 4000).
`Check.remainingUnits` and `withinBudget` retain finite search when the outer
heartbeat setting is zero; `sql.checkBudget = 0` still disables checking.
Nested SELECT phases share the remaining allowance.
No new budget option or performance threshold is required by this feature.
Use finite existing limits and process timeouts in fixtures. Record successful,
residual and exhausted cases with existing proof-cost support; the current
experiments are a feasibility baseline, not measurements of the future procedure.
Replacement proofs must elaborate under the same imports and hints without
`sql_auto`; explicit tactics such as `sql_run` can still perform rule selection.

Each case identifies whether it tests a theorem, tactic integration or the
existing model. Native SQLite comparisons are needed only where a new claim
about model conformance is made. No frozen corpus or judge lock change is implied
by adding proof rules. End-to-end acceptance includes the abstract invoices
theorem and a program-composition theorem using the new SELECT procedure.
