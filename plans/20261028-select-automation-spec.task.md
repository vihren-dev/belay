# Compositional SELECT automation: specification and experiments

Created 2026-10-28. Status: IN PROGRESS.
Audience: team. Status: [checkpoint](20261028-select-automation-spec.status.md).

## Required outcome

ADR 0027 and its accompanying specification prepare reasonably general SELECT
proof automation for implementation. The owner requests experiments and the
resolution of unclear design points before implementation. The motivating
example is a proof that selecting a NOT NULL customer column never returns NULL
on any valid database of the given schema, including a database with no rows.
The scope includes properties of collections, not only this example or unary
row predicates. No production tactic is implemented by this task.

The design explains how proved rules for source acquisition, expressions,
filtering, grouping, aggregation, projection, distinctness, sorting, slicing,
compound queries and nested queries compose. It specifies how automation uses
those rules through the existing SQL program and tactic interfaces. It preserves
SQL errors, unsupported observations, nondeterminism, parameters and execution
context. It distinguishes semantic coverage, automatic discharge and honest
residual obligations; it does not promise decision of arbitrary Lean goals.

The artifacts state observable success and failure behavior, the public claim
forms, the rule-extension mechanism, execution bridges, budgets and proof trust.
They identify which model forms are supported now and which require separate
model work. All material choices and experimental limits are visible for owner
review. The accompanying acceptance cases must expose vacuity and unsound
shortcuts, as well as successful proofs on abstract databases.

## Evidence and acceptance

Bounded Lean experiments exercise current automation and proof rules, including
the initial example and representative collection, aggregate, join, nested-query
and alternative-result cases. Experiments distinguish existing behavior from
proposed behavior. False claims and unsupported cases cannot count as successes.
Use the existing surface harness and Nix evidence paths where possible. Native
SQLite is an oracle only when an experiment concerns model conformance.

A small formal specification and semantic review cover make the trust and
completion contract reviewable. The formalization must identify assumptions and
avoid claiming that an abstract contract proves concrete tactic conformance.
All experiment processes have explicit timeouts. Each coherent commit gets
focused checks and independent review. The specification boundary requires
`just test-full` and `just verdict`; task-end checks are `just test-nix` and
`just test-scheduled-checks`. Only Nix results are acceptance evidence under the
repository rules. There are no model-prediction changes or new mutant tables in
this specification task. Required checks that cannot run remain findings.

## Existing code and constraints

Source baseline: main commit `3e2212ed6983f36144b7fc5bdce9b263f939e50f`.
Relevant surface files: `ExecutionWP.lean`, `ExecutionWPLaws.lean`,
`ExecutionSpecifications.lean`, `ReadStepRule.lean`, `SqlRun.lean`,
`SqlRunGoals.lean`, `AutoSearch.lean`, `SqlSimpLaws.lean`, `CheckAutoProof.lean`.
Relevant model files: `QueryResults.lean`, `QueryRun.lean`,
`QueryFunctions.lean`, `Subqueries.lean`, `PossibleResults.lean`, and the
`Simple*` output laws. Existing rules already handle SQL program sequencing and
all permitted execution branches. SELECT-internal rules must integrate with
those semantics rather than introduce a competing execution model.

The consumer experiments in `../belay-ux-test/QueryProgramSketch.lean` and
`SelectTableProperty.lean` establish feasibility of pure composition and a simple
table bridge. They are local prototypes, not upstream acceptance evidence.
In particular, pure `Query.results` properties alone do not establish successful
execution or cover all possible outputs. A false precondition can make a triple
vacuously true; tests must distinguish that from a usable schema-based theorem.
