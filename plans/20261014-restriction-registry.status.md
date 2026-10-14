# Status: restriction registry

Created 2026-10-14. Status: IN PROGRESS.
Task: [task](20261014-restriction-registry.task.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/Resolution/Values.lean`,
`Resolution/Resolved.lean`, `Resolution/Context.lean`, `Resolution/Resolve.lean`,
`Codec/Resolution.lean`, `packages/verifier-conformance/VerifierConformance/Predict.lean`,
`migration_check/inputs.py`, `judge/compare.py`, `docs/semantic-subset.md`.

## Findings

- 2026-10-14: about 38 resolver call sites pass free-text reasons. Users read the
  reason through `migration_check/inputs.py` and the prediction output.

## Progress

- 2026-10-14: task and status files created. The owner chose option B for question 1
  of the ADR 0012 amendment (#111): a row-dependent value for a key column is a model
  restriction; this task comes before slice 3b.
- 2026-10-14: the owner chose no CODEOWNERS change for the obligations (question 3);
  the task gains mutant-to-rule links, obligation mutants and boundary cases.
- 2026-10-14: the registry. `Resolution/Restrictions.lean` defines `RestrictionKind`
  with 39 constructors, each naming its origin; `RestrictionText.lean` gives the
  stable id, the unchanged message and the list of all kinds. A script mapped each
  message literal to one constructor (every literal matched exactly one). The type
  change of `ValueIssue.restriction`, `Restriction` and `restrict` made the compiler
  confirm every site. `Restriction` JSON keeps `reason` and adds `restriction` (the
  id); the CLI resolver, the prediction output, `conformance/predict.py` and the
  `migration_check` rejection details carry the id. The verdict counts do not change.
- 2026-10-14: documentation table of all 39 ids in `docs/semantic-subset.md`,
  `tests/restriction_registry_test.py`, `RestrictionKind.mem_all` and a check of
  distinct ids; tests of the id in the CLI report and the prediction output. The
  prediction test found a message regression from slice 3a: a REAL value in a write
  reported `affinity-conversion`; `storedValue` now reports `real-value` for it.
- 2026-10-14: `conformance/restriction_costs.py` and `just restriction-costs` count the
  claimed-corpus cases out of scope by restriction id, by frontend refusal and as
  undeclared. First result: frontend refusals dominate (statements not modeled 968,
  SELECT without FROM 483, column constraints 422, table options 313); the largest
  registry restrictions are `rowid-alias` 101 and `unmodeled-function` 85.

- 2026-10-14: owner decision on outcome 6: every restriction gets an example script,
  not a mutant; the obligation mutants run in a scheduled suite on main pushes and
  nightly runs. A probe of one script per id found five restrictions that no SQL
  reaches: four branches of `literalValue` (`negated-non-numeric`,
  `condition-as-value`, `aggregate-as-value`, `expression-as-value`), dead since
  slice 3a moved write values to query semantics, and `returning-target`, which the
  frontend blocks (DELETE ... RETURNING is refused).
- 2026-10-14: removed the four `literalValue` restrictions; query leaves and
  `defaultValue` give their values directly. `conformance/restriction_examples.py`
  has one example script per id (35); `tests/conformance_restriction_examples_test.py`
  (harness suite, about 2 s) runs each through the frontend and the resolver;
  `returning-target` is listed as frontend-blocked until slice 3c.
- 2026-10-14: mutant links. Each mutant table has `GUARDS`; `conformance/mutant_guards.py`
  checks that a `rule:` guard names the declaration that contains the mutant's text, and
  that restriction and obligation guards exist. All 45 existing mutants guard rules.
- 2026-10-14: obligation mutants. `conformance/obligation_mutants.py` lists 13 conjuncts of
  `insertReady`, `updateReady` and `statementReady`. Only three can be violated by a
  native state that resolution accepts; they have mutants and boundary cases in
  `conformance/authored_obligations.py` (a REAL 1.0 in an untyped unique key under
  INSERT and UPDATE, and under the filter `c = 1`). The two key checks of `updateReady`
  cover each other, so one mutant removes both. Seven conjuncts repeat a resolution
  restriction, and three have a recorded reason (row width is a resolution theorem;
  the largest-rowid case is random in SQLite). The scheduled suite
  `scheduledTests.obligations` (about 18 s) runs in `just package`, not on pull
  requests. `conformance/obligation_evidence.py` writes corpus version 10.

## Remaining

- Full checks, CI timing, pull request A; later the judge PR that claims corpus 10.
