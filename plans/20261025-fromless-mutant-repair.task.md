# Restore the SELECT-star mutation check

Created 2026-10-25. Status: OPEN.
Audience: implementers and reviewers.
Progress: [status](20261025-fromless-mutant-repair.status.md).
Specifications: [queries without FROM](20261016-select-without-from.task.md),
which requires the suite to notice acceptance of `*` without FROM; ADR 0008
mutation evidence and the current package boundaries.

## Present problem

PR #249 Linux general-mutant CI failed. A focused Nix reproduction on its
published source confirms that `fromless_star_accepted` survives the existing
`fromless-star` target. `starIssue` rejects the query before the changed
`resolveResultColumn` guard runs. Both production guards have valid callers;
the fault belongs in the mutation description, not the production resolver.
A disposable two-site probe retains the same baseline and kill assertions
and is killed by the existing target. Query and JSON mutant groups passed
separate local reproductions; their hosted failures remain unexplained.

## Required outcomes

- The existing logical fault, accepting unqualified `*` without FROM, changes
  both rejection sites in one isolated mutant. Its name, native target,
  baseline AGREE requirement and kill assertion remain intact. The other
  fromless faults retain their behavior.
- The shared mutation harness can apply the required group of source edits
  to one copy. Every edit must match exactly once. A stale or repeated anchor
  produces an actionable error naming the mutant and affected file before
  classification. A rejected mutation must not modify the shared base.
- The guard audit checks the relation between each changed source fragment
  and the rule it names. A grouped mutation must not hide an unchecked second
  edit. Existing restriction and obligation guards retain their meaning.
- All existing single-edit mutant tables continue to run through the common
  harness. Use the smallest explicit representation needed for this fault;
  no second mutation runner or general plugin framework.
- Production Lean, native cases, judge claims and frozen evidence remain
  unchanged. Do not remove mutations or targets, weaken assertions, raise
  timeouts, or claim to repair unconfirmed hosted timing failures.

## Observable tests and acceptance

- Bounded Python tests exercise one edit and a group, including successful
  application to one isolated copy, missing and duplicate anchors in each
  position, and a bad rule link on the second edit. Verify the base remains
  unchanged and classification does not run after validation failure.
- The real mutant guard inventory passes. The focused Nix fromless group
  retains native baseline agreement and kills all its existing mutants,
  including the repaired star fault. A representative existing single-edit
  group passes through the same harness. Every subprocess has a timeout.
- Run the relevant harness tests and independent review per commit. At task
  acceptance run the full Nix suite, verdict, Nix checks and scheduled checks.
  Only named relevant mutant groups run locally, never the broad mutant suite.
  Compare protected source trees to establish unchanged production semantics.
- Retain the published-source failure and the repaired focused Nix evidence,
  with precise source revisions. Hosted CI status is reported separately.

## Relevant code and constraints

`conformance/resolve_mutants.py` owns copy/build/classify and `measure`.
`conformance/fromless_mutants.py` describes this fault and its target.
`conformance/mutant_guards.py`, `tests/mutant_guards_test.py`,
`tests/mutant_sets.py` and `tests/conformance_query_mutants_test.py` are the
shared audit and execution callers. Update their types and package source
selection when required. Read other callers before changing the representation.

On published PR #250 both guards use `scope.inner.isEmpty` in
`Resolution/Queries.lean` and `Resolution/CompoundTerms.lean`. The queued view
integration changes both predicates to `!(scope.inner.any (·.namesVisible))`.
Carry the anchors mechanically when that source joins; do not change the
production guards to preserve a mutation. Keep this repair on the published
base so it can be reviewed and released independently of the view task.
