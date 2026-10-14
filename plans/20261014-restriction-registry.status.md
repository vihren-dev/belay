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

## Remaining

- Cost report; mutant links; obligation mutants and boundary cases.
