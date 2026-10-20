# Status: the JSON functions that build or edit text (ADR 0015, slice 3)

Created 2026-10-20. Status: open.
Task file: [task](20261020-json-edit-functions.task.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D5.

## Progress

- 2026-10-20: the C code of SQLite 3.51.0 read: `jsonAppendSqlValue`, `jsonFunctionArgToBlob`,
  `jsonInsertIntoBlob`, `jsonLookupStep` in edit mode, `jsonCreateEditSubstructure`,
  `jsonMergePatch`, `jsonTranslateBlobToPrettyText`, `jsonErrorFunc`, `jsonArrayStep` and
  `jsonObjectStep`.

- 2026-10-20: the scalar functions of the slice ("JSON build and edit functions").
  - Lean: `Json/Edit.lean` (`editStep`, `editMember`, `createSubstructure` with fuel),
    `Json/Build.lean` (`sqlValueText`, `sqlValueNode`, `jsonArray`, `jsonObject`, `jsonEdit`,
    `jsonRemove`), `Json/PatchPretty.lean` (`mergePatch`, `prettyNode`, `jsonPretty`,
    `jsonErrorPosition`), `Json/BuildExamples.lean`; `Json.apply` takes each argument with its
    subtype; `Expr.givesJson` and `Arguments.givesJson` in the evaluation block; new
    `JsonError` constructors with SQLite's messages; `ExprFault.lean` holds the parts of
    `ExprEval.lean` that are not recursive.
  - Resolution: the names and arities in `Resolution/Calls.lean`; the restriction
    `json-subtype` (`Resolved.Expr.subtypeUndescribed`) for value arguments passed on through
    `coalesce`, `iif`, `nullif`, `min` or `max`.
  - Native: subqueries, views and CTEs drop the subtype; a direct call, unary `+`, `nullif`,
    `max`, `CASE` and `coalesce` keep it. A BLOB argument is JSONB (`json_array(x'01')` is
    `[true]`), so it stays a `may` fault; the task text was amended.
  - `conformance/authored_json_edits.py`: 13 cases, all agree (kernel proofs in
    `conformance_query_coverage_test`); `json_edit_evidence.py` (corpus 38);
    `json_edit_mutants.py`, all killed.
  - Tests run: `function_catalog`, `test_model_package` (164 modules), `mutant_guards`,
    `restriction_registry`, `conformance_restriction_examples`, `restriction_costs`,
    `conformance_authored`, `conformance_predict`, `conformance_query_coverage`,
    `test_lean_categories`, the JSON edit mutants.

## Remaining

- The aggregates `json_group_array` and `json_group_object`.
- Review, the slice verdict, corpus 38, `just test-full`.
