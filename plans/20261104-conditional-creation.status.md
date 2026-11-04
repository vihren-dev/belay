# Conditional table and index creation: task status

Date: 2026-11-04. Status: OPEN.
Audience: the implementation team.
Task: [Conditional table and index creation](20261104-conditional-creation.task.md).
Specification: [ADR 0030](../docs/adr-0030-conditional-creation-and-expression-grouping.md).
Source baseline: main `528ea92`.

Relevant files: `packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/Syntax.lean`,
`Resolution/Definitions.lean`, `Resolution/ViewDefinitions.lean`, `Resolution/StatementArms.lean`,
`packages/belay-sqlite-text/Belay/Sqlite/Translation/Tables.lean`, `Translation/Schema.lean`,
the theorems that the ADR's context lists, `tests/syntax_mapping_test.py`,
`conformance/requirement_cases.py`, `docs/semantic-subset.md`.

## Progress

- 2026-11-04: task specified; ADR 0030 accepted by the owner.
- 2026-11-04: the model, the translation, the proofs, the documentation and the tests of the
  slice in one commit. New: `Resolution/ConditionalCreation.lean` (the no-op conditions and
  resolvers), `ConditionalCreationSteps.lean` (with a free name the clause changes nothing),
  `resolvedStepOutput_drop_nil` and the generalised `runScriptStep_createIndex_ok_iff`,
  `Script.createIndex_allOk_iff` and `Succeeds.iff_createIndex`. The stored cases of
  `conformance/cases` and the regression case get `"ifNotExists": false`, since the derived JSON
  decoder reads no default; the regression's `mismatch.json` gets the new case hash. The
  editor's table origins (`SqlTableOrigins.lean`) give no place for `CREATE TABLE IF NOT
  EXISTS`, which may do nothing. Authored corpus module `conformance/authored_conditional_creation.py`
  (32 cases, version 7 records; every case agrees, and so do the promotions of the
  task); its freeze and claim go into the claims pull request.
  Tests of the commit: `tests/syntax_mapping_test.py`, `tests/conformance_model_test.py`,
  `tests/conformance_conditional_creation_test.py`, `tests/surface_conditional_creation_test.py`,
  `tests/surface_success_test.py` (the create-index and unique-email examples),
  `tests/conformance_generation_test.py`, `tests/surface_editor_origins_test.py`.
