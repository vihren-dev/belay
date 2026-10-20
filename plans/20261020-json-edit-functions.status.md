# Status: the JSON functions that build or edit text (ADR 0015, slice 3)

Created 2026-10-20. Status: open.
Task file: [task](20261020-json-edit-functions.task.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D5.

## Progress

- 2026-10-20: the C code of SQLite 3.51.0 read: `jsonAppendSqlValue`, `jsonFunctionArgToBlob`,
  `jsonInsertIntoBlob`, `jsonLookupStep` in edit mode, `jsonCreateEditSubstructure`,
  `jsonMergePatch`, `jsonTranslateBlobToPrettyText`, `jsonErrorFunc`, `jsonArrayStep` and
  `jsonObjectStep`.

## Remaining

- All outcomes and tests.
