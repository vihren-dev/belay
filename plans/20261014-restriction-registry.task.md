# Restriction registry

Created 2026-10-14. Status: IN PROGRESS.
Requested by the owner on 2026-10-14, before slice 3b of ADR 0012, so that the
restrictions of slice 3b are recorded from the start, and so that the admission
obligations are checked by evidence (owner decision on question 3 of the ADR 0012
amendment, #111). Related: ADR 0008 (model
restrictions, R7), ADR 0012 and its amendment for row-dependent writes,
`docs/semantic-subset.md`.

## Outcome

A model restriction is SQL that SQLite accepts but the model does not describe. Today
each one is a free-text reason at its resolver call site. After this task:

1. **One registry.** Every model restriction of name resolution is a constructor of
   one enumeration, with a stable id, the message that users read, and a docstring
   that names the decision that introduced it (ADR, slice or owner decision). The
   resolver refers to restrictions only through the enumeration; no free-text reason
   remains.
2. **Unchanged behavior.** Every message that users see is the same text as before,
   at the same path. No resolution result, verdict or proof changes, apart from the
   restriction values themselves.
3. **Ids in the outputs.** The prediction output and the frontend rejection carry
   the restriction id next to the message. The judge does not change: it ignores
   the new field, and a judge change would need its own owner-approved PR.
4. **Documentation that cannot drift.** `docs/semantic-subset.md` has a table with
   one row for each restriction id. A test fails when an id has no row, or a row no
   id.
5. **A cost report.** A command counts, for each restriction id, the cases of the
   claimed corpora that it makes `MODEL_UNSUPPORTED`, from the subject's predictions
   (`nix-build integrity/judge.nix -A predictions`).
6. **Mutants name what they guard.** Each mutant of `resolve_mutants.py`,
   `query_mutants.py`, `number_mutants.py` and `write_mutants.py` names the rule,
   restriction or obligation that it guards. A test checks that every restriction
   id and every conjunct of the admission obligations has at least one mutant, and
   that every mutant names something that exists.
7. **Obligation mutants and boundary cases.** Each conjunct of `insertReady`,
   `updateReady` and `statementReady` has a mutant that removes it, and an authored
   boundary case whose database state is just outside the domain: with the conjunct
   the case is `MODEL_UNSUPPORTED`, without it the case disagrees with native SQLite.
   Examples: `1.0` in a column without affinity under the filter `c = 1`; a REAL that
   equals an integer in a unique key column. The boundary cases form a new coverage
   corpus for a later judge change (owner decision of 2026-10-14 on question 3 of
   the ADR 0012 amendment).

## Tests

- The registry test: the ids are unique and stable in form, every id has a row in
  the documentation table, and every row has an id.
- The existing resolution examples and conformance tests pass unchanged where they
  compare behavior; examples that compare restriction text compare constructors or
  messages.
- A test of the prediction output and of the frontend rejection that the id is
  present.
- A test of the cost report over a small fixed set of predictions.
- The mutant link test, and the obligation mutants against their boundary cases.

## Key points for the implementer

- **Where restrictions are made.** `ValueIssue.restriction (path) (reason : String)`
  (`Resolution/Values.lean`), `Restriction { statement, path, reason }`
  (`Resolution/Resolved.lean`) and `restrict index path reason`
  (`Resolution/Context.lean`). About 38 call sites pass literal reasons, and a few
  build them from parts. `Resolve.lean` builds one `Restriction` directly.
- **Readers of the reason.** `VerifierConformance/Predict.lean` emits
  `{"restricted": reason}`; `migration_check/inputs.py` puts `result["reason"]` into
  the user's rejection; `conformance/predict.py` passes the prediction on, and the
  locked judge (`judge/compare.py`) reads it, so the new field must leave its
  reading unchanged. The JSON of `Restriction` is derived in `Codec/Resolution.lean`.
  Keep the message field so that these readers keep their meaning, and add the id.
- **Proofs.** Lemmas match `.restriction path reason` with variables and mostly do
  not depend on the reason. `ErrorKinds.lean`, `OperandIssues.lean` and the rule
  modules state that issues are restrictions; check them after the type change.
- **Mutants.** `conformance/query_mutants.py` and `resolve_mutants.py` replace
  prepare errors with `.restriction [..] "mutant"`; they need a constructor.
- **Frontend refusals are a separate layer.** Syntax without a constructor is refused
  in Python (`syntax_*.py`, `absent`, `tree.unsupported`). This task covers the
  resolver's restrictions; the documentation table may list frontend refusals
  separately, without ids.
- **File size.** The enumeration with ids and messages may exceed 200 lines; split it
  by area (definitions, values, writes, queries) if needed.
