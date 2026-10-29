# ADR 0027: Compositional SELECT proofs

Date: 2026-10-28; revised 2026-10-29. Status: DRAFT; experiments checked, owner review pending.
Audience: designers and reviewers. Number 27 was explicitly requested by the owner.
Evidence: [semantic review cover](select-automation-review.md), [source map](select-automation-source-map.md).
Related: [ADR 0017](adr-0017-user-surface.md),
[ADR 0018](adr-0018-surface-sql.md), [ADR 0022](adr-0022-database-validity.md),
[ADR 0026](adr-0026-semantic-proof-boundaries.md).
Acceptance contract: [SELECT automation](select-automation-acceptance.md).
Retirement inventory: [replaced code](select-automation-retirement.md).
Investigation: [task](../plans/20261028-select-automation-spec.task.md).

## Intent and current boundary

The owner proposes proving a SELECT property by tracing how each evaluation
phase transforms propositions, forward or backward, then automating that process
through `sql_auto`. The owner requests reasonably full generality, not only the
motivating NOT NULL projection. This ADR interprets that as general proof rules
over the existing model and a specified automatic fragment. It does not require
new SQLite semantics or decision of arbitrary Lean propositions.

At source `3e2212ed`, Belay already has `Sql.check`, a predicate transformer,
`Std.Do` triples, `mvcgen` specifications, and sequencing rules. `sql_run` traverses
programs. For SELECT it applies `Sql.check_query_select`, `check_single_select`
or `check_send_select`, leaving model-coverage and selected-output obligations.
`sql_auto` tries commute, run and grind routes. `sql_simp` has expression,
resolution and calmness laws. None of these facts implies a general internal
SELECT proof procedure exists. The new work extends these interfaces.

The model computes source rows, filters them, constructs records, applies
DISTINCT, sorts and slices. `records` combines grouping, aggregate evaluation,
HAVING, projection and sort-key evaluation. `Query.results` selects one result;
`Query.possibleResults` and execution branches describe permitted alternatives.
Faults and coverage are separate from pure result computation. A theorem about
`Query.results` alone is not a theorem about successful SQL execution.

## D1. One semantic foundation, arbitrary postconditions

The public general contract remains `Sql.check` and its standard triples, with
arbitrary postconditions on returned values and the full reached context.
Rules quantify over all execution branches and selected outputs as the existing
contract does. SQL errors can satisfy an explicitly error-accepting postcondition;
an unmodeled stop cannot satisfy `Sql.check`. A postcondition of `True` does not
assert SQL success. No new interpreter, branch relation or competing SQL monad
is introduced.

Internal rules accept predicates over complete collections and intermediate
types. A row predicate is a convenience, not a restriction. Group counts,
multiplicity, sortedness, uniqueness, cross-row relations and existential
witnesses must remain expressible. A rule for a pure function can use the form
`∀ input, P input → Q (phase input)`; effectful rules retain the existing outcome
and context semantics. Composition, consequence and conjunction rules let a
user refine or combine specifications without changing the query.

## D2. Successful-row conveniences

Provide `Run.returnsResult Q` for a complete-result predicate and
`Run.returnsRows P` as its row-wise specialization. Require `run.value.isSome`
and one successful row observation: `.rows rows` satisfies `Q rows`; a nonempty `.oneOf choices`
satisfies it exactly when every permitted row list satisfies Q. Errors,
unmodeled outcomes, `.done`, missing outputs and multiple statement outputs fail.
The exact connection to `OutputChoice`, including raw versus concrete choices,
must be proved. Reject empty alternative lists rather than accept them vacuously.

The local UX prototype's `returnsRows` accepts only `.rows`; it is not a public
API. The upstream convenience deliberately covers modeled alternative results.
Raw `Sql.check` remains available for other observations, including error claims
and multiple statements. A success-requiring postcondition on `query` accepts
only `.ok rows` and applies Q to those rows. `single` retains its existing
`none` cases. No adapter silently interprets `none` or an error as empty rows.

These predicates describe the outputs of that run. Equivalence with a
branch-universal success claim applies to one SELECT observation with a
context-independent row-list predicate and explicit statement/context premises.
For arbitrary programs, use `Sql.check_actual` to obtain the actual returned
value and its postcondition; outputs alone give no reverse implication.
A continuation can differ across choices. Context-sensitive
posts must also handle the raw `.oneOf` trace, not only concrete `.rows` traces.

Row properties use positional `List Value` at the primitive boundary. A cell
existence claim is distinct from `row[i]? ≠ some .null`, which also admits a
missing cell. The motivating acceptance theorem establishes existence and
non-nullness. Generated named-row types are not required by this feature.

The ADR 0017 S2 names `Holds`, `Empty` and `Fails` remain, as the owner decided
on 2026-10-29. Each becomes an abbreviation of the observation predicates of this
decision: `Holds` and `Empty` of the successful-result predicate, `Fails` of the
matching error observation. Each has the same truth value as its current
definition on every query script and database; the implementation proves that
equivalence as a migration witness, then deletes the old definitions. The
decidable instances and the `check_query` argument are kept. Their consumers in
the claims driver, assertions, explanations and migration patterns change no
statement. There is one claim vocabulary, not two.

## D3. General decomposition, bounded automatic closure

Every SELECT form that the current model describes has a public semantic
decomposition route. This includes sources and joins, WHERE, grouping,
aggregates, HAVING, projection, DISTINCT, ordering, slicing, compounds and
subqueries. Rules may expose expression, context, certainty or coverage premises.
A fallback that merely repeats the original whole-query proposition does not
count as decomposition. The operator inventory and tests identify each route.

The automatic acceptance cases define a separate promise: with their documented
schema and data hypotheses, `sql_auto` closes them without a supplied theorem
of the whole query. Every operator family has a representative automatic case.
The promise is staged, as the owner decided on 2026-10-29. Decomposition rules
are required for every family. Automatic closure is required first for the
core set A01 to A04, A08, A10, A13 and A14; the remaining automatic cases are
later slices. Retirement of a family's replaced code follows its decomposition
rules and acceptance cases, not its automatic closure.
This does not promise closure for arbitrary predicates or expression programs.
An unsolved arithmetic, Lean user-function or collection fact remains an explicit
obligation. An unsupported model form remains a model restriction. Neither is
a counterexample. The existing model's admission and restriction boundary stays
fixed; this ADR does not silently add window functions or other missing syntax.

## D4. Phase rules retain SQLite meaning

Schema facts come from validity and explicit table/column identification. A
fixed catalog equality can be a convenience; generic schemas and table-presence
premises remain supported. The tactic must not infer validity from a table name.
CHECK permits NULL; WHERE and HAVING require SQL TRUE. Type, affinity and
collation rules come from the model, not host arithmetic or Lean equality.

Filtering carries membership and its truth condition. Projection relates each
output cell to its expression value. Groups retain input membership, key
equivalence, multiplicity and the distinction between zero groups and one empty
aggregate group. Aggregate rules include NULL behavior and fault obligations.
Join rules retain concatenation, ON truth, multiplicity and outer-join NULL
extension. DISTINCT and compounds use the model's comparison and representative
restrictions. A scalar subquery with no row can produce NULL.

Records carry output cells and sort keys. Sorting preserves records; slicing
can remove them. Rules about output membership are distinct from rules about
sequence order and cardinality. Ordering ties and cut boundaries use every
permitted result. A representative stable sort cannot prove a unique winner.
An ordering or equality conclusion uses the observable order convention of the
model, not an invented physical scan order.

## D5. Sources, contexts and execution

Source acquisition is a proof phase, including table scans, joins, derived
tables, modeled CTE/view expansion, table-valued sources and correlated sources.
Subquery specifications are indexed by the enclosing row and evaluation context.
The first-cell, first-column-multiset and complete-row certainty conditions remain
distinct. Derived-source certainty is not weakened to make an example succeed.

Execution adapters carry parameter values, connection state, clock, statement
index and initial-origin database where applicable. A read after a write uses
the reached context. Source faults, expression faults, aggregate overflow and
LIMIT/OFFSET binding errors cannot disappear through a pure-value proof.
Fault conditions follow modeled evaluation demand, not an invented rule that
every expression of every discarded row must execute.
In particular, `Query.outputOn_clean` alone permits `.may` faults. Execution
bridges retain `Query.described`/statement readiness, plain nested subqueries,
absence of `.may` source/run faults, and derived-source ending/certainty checks.
`EvalContext.Quiet` alone does not establish complete-row source certainty.
Preparation errors use the existing error route; no resolved query is invented
when SELECT resolution returns `.prepareError`.

## D6. Tactic integration and extension

Add SELECT-obligation processing to `sql_run` and expose it as `sql_select` for
standalone query-result and phase goals. `sql_auto` reuses this procedure through
its existing bounded search and adds a route for successful-result conveniences.
Program sequencing remains the job of `sql_run`; nested SELECT sources are not
script concatenation. Standard triples and conditions left by `mvcgen` work too.

The procedure recognizes the goal and resolved shape, applies a matching proved
rule, extracts schema hypotheses, and discharges routine expression obligations
with existing simplification and suitable Lean solvers. It can propagate facts
forward or pull a postcondition backward. No fixed direction is public behavior.
The tactic must not search concrete database samples to prove a universal claim.

Users can pass proved lemmas as hints and apply all rules manually. A named
phase-tagged rule attribute groups decomposition rules. Explicit hints run in
supplied order, then registered theorems in qualified declaration-name order.
Its matching and registration contract is specified in the acceptance document. Registered
rules are Lean theorems, not trusted executable certificates. Cyclic rules or
unhelpful hints cannot evade budgets. Registration does not automatically add a
lemma to global simp or grind sets. Existing hint syntax remains usable; theorem
application must preserve all premises. A user-defined rule and a manual proof
must each demonstrate that the automatic fragment is not the only interface.

## D7. Failure, budgets and trust

`sql_select` and `sql_run` leave typed residual goals with a phase-specific
explanation. Unknown shape, unsupported observation, unsolved premise and budget
exhaustion have distinct explanations. `sql_auto` reports success only when the
original goal has a complete proof. Failed search restores the original goal and
sibling goals. Budget exhaustion is not falsehood and produces no proof claim.

Use the existing SQL work budget, cancellation and recursion controls. Nested
phase searches share the caller's budget rather than replenish it. Successful
automation offers explicit steps that elaborate again without the top-level
`sql_auto` route search; explicit tactics can still select phase rules. Every
route produces an ordinary Lean proof checked under the current dependency
policy; no `sorry`, new axiom or native decision bypass is introduced.
The background checker reuses this search for the new claim shapes without
weakening certification, exclusions, replay or command-level cancellation.

## Scope and supersession

The project has no users. The phase rules replace the per-form proof layer, and
replaced code is deleted; there are no compatibility aliases. The
[retirement inventory](select-automation-retirement.md) names each file as
required, candidate or retained, and the implementer migrates every caller
before a deletion.

On adoption, this ADR supersedes:

- The ADR 0017 S4 query-form theorems (`CountQuery`, `AggregateQuery`,
  `ColumnQuery`, `SelectOneFrom`, `SelectNoFrom`, `ExistsQuery`,
  `NotExistsQuery`, `DuplicateKeyQuery`, `FilteredDuplicateKeyQuery`,
  `UniqueLookupQuery` and their may-fail and shared-case companions). Each is a
  whole-query lemma. Their claims become acceptance cases and their negative
  examples become the "required contrast" column.
- ADR 0026 D1, the per-family complete-output characterizations completed in
  PR 297. A phase decomposition replaces a per-family characterization. ADR
  0026 D2 to D6 are unaffected.
- The `Query.Simple` predicate and its laws. `Simple` is a phase decomposition
  of one shape; its laws become the `filter` and `project` rules.

The mathematical claims of the superseded code remain obligations, as in ADR
0025 D4: the acceptance cases and the retained phase rules must derive each
retired claim with the same entry assumptions. Historical task and status
records keep their original wording. The per-family resolution-shape laws are
not superseded: the ADR 0026 D3 certificate takes successful resolution as a
premise and does not give the resolution equation. They stay, except a law
whose every consumer is retired, which the status file records.

## Consequences and validation

The rule library replaces the per-form layer around the current evaluator; some
fused functions need characterization lemmas rather than evaluator refactors.
The first implementation can be incremental. Completion requires decomposition
rules for every family, automatic closure of the core set of D3, and an empty
required column of the retirement inventory. Model-semantic changes discovered
during proof work require their own explicit specification and conformance
evidence. The status file records the net line change at completion.
This follows the [Lean simplification goal](lean-simplification-goal.md):
replace duplicated proofs with general rules while preserving capabilities.

The accompanying acceptance contract names positive, negative and residual cases.
Retained experiments test feasibility and current boundaries, not the existence
of the proposed tactic. All recommendations above remain draft until reviewed
with the experiment results and the formal semantic cover.
