# SELECT automation: semantic review cover

Date: 2026-10-28; revised 2026-10-29. Status: DRAFT; Lean experiments checked, owner review pending.
Audience: designers and reviewers.
Related: [ADR 0027](adr-0027-compositional-select-proofs.md),
[acceptance contract](select-automation-acceptance.md).

The owner selected Lean-only specification artifacts. The formal statements
are the existing Lean execution contract and the retained Lean experiments.
There is no separate SQL interpreter or assumed abstract soundness predicate.
No Isabelle or PDF build is required for this revised artifact choice.

## Formal contract and evidence boundary

[`Sql.check`](../packages/belay/Belay/Sqlite/ExecutionWP.lean) quantifies over
every permitted branch. A stopped branch makes it false. A returning branch
must satisfy the supplied postcondition at its full reached context. SQL errors
can return values, so a postcondition of `True` does not establish SQL success.
`Sql.check_actual` rules out an empty-branch interpretation: a checked program
has an actual returned value satisfying the postcondition.

`Sql.check_bind`, `Sql.check_mono` and `Sql.check_and` supply composition,
consequence and conjunction. Their predicates are arbitrary Lean propositions.
A postcondition on a `query` result can constrain an entire collection, its
cardinality or relations between rows. It need not be a per-row predicate.
[`ReadStepRule.lean`](../packages/belay/Belay/Sqlite/ReadStepRule.lean) retains
modeled execution and universal selected-output obligations for SELECT.
[`OutputChoice`](../packages/belay/Belay/Sqlite/ExecutionBranches.lean) includes
both the actual output and each concrete alternative of an `oneOf` output.
The raw wrapper remains observable to continuations and in the output trace.

The proposed conveniences and automation must refine these definitions.
[`AutoSearch.lean`](../packages/belay/Belay/Sqlite/AutoSearch.lean) currently
checks proof completion, bounds search and restores failed routes. The
experiments below passed their Nix Lean checks and establish the stated properties
and current limitations. They do not prove that the proposed tactic exists
or meets the automatic acceptance matrix. Fixture paths refer to the retained
experiment files; the task status records their validation and integration.

## Complete execution views

Each downward view fixes the program, input and environment in the cited
fixture and retains **all** permitted executions of that program. Its semantic
view is this complete execution family; its review artifact is the named Lean
theorem and the explanation below. This is refinement of the execution
semantics used by the draft, not a claim that a complete future automation
implementation has been constructed. A prohibited claim is shown beside its
closest admitted execution view.

| View and direction | Concrete artifact | Design axis and surprising consequence |
| --- | --- | --- |
| Empty customer table; downward execution view | [SelectAutomationSchema.lean](../tests/surface/SelectAutomationSchema.lean), `emptyCustomers`, `customerQuery`, `schema_witnesses`, `schema_instances` | The query succeeds with no rows. Every returned cell can be non-NULL without any cell existing. Nonempty output is a different claim. |
| One customer; downward execution view | Same file, `oneCustomer`, `customerQuery`, `schema_witnesses`, `schema_instances` | The same schema also permits a returned cell. `schema_instances` supplies every premise of `schema_projection` for both databases and applies that theorem. The demonstration relies on neither an impossible schema premise nor only empty output. |
| One-row window over two rows; downward execution view | [SelectAutomationExecution.lean](../tests/surface/SelectAutomationExecution.lean), `sample`, `readOne`, `all_choices_succeed`, `representative_is_insufficient` | Every permitted result has one non-NULL row. The first-value-only claim is false. A proof about one representative result cannot establish the universal execution claim. |
| Malformed JSON read; downward execution view | Same file, `failingRead`, `error_is_not_success`, `false_precondition` | A modeled SQL error fails a success postcondition but satisfies an explicit error-accepting one. A triple with precondition `False` proves nothing about a usable database. |
| Preparation failure; downward execution view | Same file, `sample`, `preparation_error` | `SELECT absent FROM missing` returns modeled error code 1. A resolution failure is not automatically an unsupported stop or empty success. |
| Read in a continuing context; downward execution view | Same file, `prior`, `continuing_context` | The query reads the existing counter and indexed clock. It retains the prefix, settings and open transaction, and advances the statement index. A fresh-run proof would not establish this claim. |
| Sent one-row window; downward execution view | Same file, `prior`, `raw_wrapper_required` | A postcondition accepting both concrete row outputs still fails if it rejects the raw `oneOf` output. Concrete choices do not replace the raw observation. |
| Read of `sqlite_schema`; downward execution view | [S6RulesNegativeCertificates.lean](../tests/surface/S6RulesNegativeCertificates.lean), `schemaRead`, `initial`, `schema_read_ends_run`; [SelectAutomationExecution.lean](../tests/surface/SelectAutomationExecution.lean), `unsupported_is_not_vacuous` | The concrete schema read stops unmodeled. The general stopped-step theorem then excludes even `True`. This is an inhabited unsupported case, not an assumption that some unsupported step exists. |

The zero, one and many boundaries are visible: zero successful rows, one
successful row, and several permitted one-row results. Failure is separate from
empty success. An empty alternative list must not establish successful rows
vacuously; the proposed convenience needs its own negative acceptance case.

## Generalized proof and evaluator views

These views expose what pure laws and sound search alone permit. Each removes
an execution or automatic-closure obligation from the full draft. Thus it is
an upward view, not evidence that the removed obligation has been met.

| Whole semantic view and direction | Concrete artifact | Consequence and omitted obligation |
| --- | --- | --- |
| Existing SELECT evaluator with an arbitrary source list and evaluation context; upward from successful execution | [SelectAutomationCore.lean](../tests/surface/SelectAutomationCore.lean), `collection_count`, `where_fact`, `where_nonnull`, `duplicates_remain`, `aggregate_empty`, `every_window_result` | Collection and filtering facts are expressible; duplicates matter; an ungrouped empty aggregate returns count zero and NULL sum. Source acquisition, failure freedom and execution alternatives still need the actual execution bridge. |
| Existing source evaluator with the complete fixed nested/join fixtures; upward from a successful outer program | [SelectAutomationSources.lean](../tests/surface/SelectAutomationSources.lean), `nested_projection`, `nested_uncertainty`, `nested_ordered`, `join_null_extension`, `nested_fault` | First-column certainty does not establish complete derived-row certainty. Ordering can make the source usable. An outer join can introduce NULL despite non-NULL right input, and a source fault is not an empty successful source. These are evaluator facts, not whole-program success proofs. |
| Current bounded `sql_auto` together with its ordinary proof obligations, without the new automatic acceptance promise; upward from the proposed feature | [SelectAutomationSchema.lean](../tests/surface/SelectAutomationSchema.lean), `schema_projection` | The theorem starts with `fail_if_success sql_auto [db.notNull]` and then proves the claim by existing laws. Failure of this search is compatible with truth of the claim. The new acceptance matrix, not soundness alone, excludes an implementation that always leaves the goal open. |

The schema theorem has explicit resolution, table, column and calmness
premises. It is not an unqualified theorem about every SQL string or every
schema. Its proof establishes cell existence as well as non-nullness; a missing
cell must not count as a non-NULL cell.

The unsupported-source examples distinguish a current model boundary from a
missing proof rule. The schema example distinguishes search incompleteness
from a false proposition. A timeout is a third case: it supplies neither a
counterexample nor a completion proof. Residual-goal and rollback assertions
remain the explicit acceptance obligations in the draft, not consequences of
the pure evaluator examples.

## Scope of this cover and remaining review choices

Together, these views expose arbitrary collections, vacuity, failures,
alternatives, source certainty and incomplete search. They do not enumerate all
SQL syntax. The [acceptance matrix](select-automation-acceptance.md) supplies
the required aggregate, compound, correlated-source, parameter, ordering and
context cases. In particular, a correlated-source rule must be indexed by the
outer row; the nested-source examples do not prove this requirement. A read
after a write must use the reached context. These are required implementation
tests, not optional extensions inferred from this review cover.

The draft's recommendations remain subject to owner review: success-requiring
collection conveniences with raw `Sql.check` preserved; semantic decomposition
for current modeled phases; a bounded automatic closure matrix; explicit
residual obligations; and proof-rule hints plus manual application. The existing
public resource options are retained; no new performance thresholds are proposed.
Public convenience names, the separate tactic
entry point and the rule-registration interface are draft interface choices.
No validation failure by itself authorizes changing these intended semantics.

A finite Z3 projection is not used. The retained contract quantifies over
arbitrary Lean propositions, unbounded lists and execution contexts. A bounded
encoding would check a different claim and would not establish faithfulness
of this higher-order contract. The Lean statements and their actual dependency
checks are the formal artifact chosen by the owner.

The owner can accept this complete cover, return statements that clarify
intent, request a different cover without changing intent, or combine
clarifying statements with a request for a different cover.
