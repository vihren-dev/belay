# The JSON functions that build or edit text (ADR 0015, slice 3)

Created 2026-10-20. Status: open.
Status file: [status](20261020-json-edit-functions.status.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D5.

## Process

As for slices 1 and 2: local jj commits with the tests that touch each one; at the end of the
slice the local verdict, the corpus, and `just test-full`.

## Outcome

1. **Functions.** `json_quote`, `json_array`, `json_object`, `json_set`, `json_insert`,
   `json_replace`, `json_remove`, `json_patch`, `json_pretty` and `json_error_position`, and the
   aggregates `json_group_array` and `json_group_object`, as SQLite 3.51.0 computes them
   (checked natively):
   - `json_quote`, `json_array`, `json_object` and the aggregates write each SQL value as JSON
     (`jsonAppendSqlValue`): NULL as `null`, an integer in decimal, a REAL by `%!0.15g`, text
     as a JSON string with SQLite's escapes, JSON text (see 2) as it is, and a BLOB fails with
     `JSON cannot hold BLOB values`; `json_object` labels must be text (`json_object() labels
     must be TEXT`), and an odd number of arguments fails;
   - `json_set`, `json_insert` and `json_replace` parse the JSON, then apply each path and
     value in turn: a NULL path is skipped, a path that does not start with `$` is a bad
     path, `$` alone replaces the whole value for `json_set` and `json_replace`; a missing
     member or `$[#]` element is created by `json_set` and `json_insert`, with objects and
     arrays for the rest of the path; an array index past the end is not created;
   - `json_remove` removes each path; a NULL path gives NULL, and `$` gives NULL;
   - `json_patch` is SQLite's RFC 7396 merge patch;
   - `json_pretty` writes the JSON with an indent (four spaces by default) per level;
   - `json_error_position` is 0 for well-formed JSON text and NULL for NULL.
2. **JSON subtype.** An argument is JSON, not text, when it is a direct call of a function that
   gives JSON (`json`, `->`, the functions of this slice, and `json_extract` when it selects an
   array or an object). The model decides this when the statement runs. An argument that is
   another expression with a JSON call inside, such as `coalesce(json(x), y)`, is the
   restriction `json-subtype`, because the model does not describe how SQLite keeps the subtype
   through other expressions.
3. **Out of the slice.** JSONB arguments (BLOBs) stay as today, a `may` fault, until slice 4. The
   position of `json_error_position` for malformed JSON is not described: the model gives a
   `may` fault, so such a case is out of scope.

## Tests

- Lean examples of each function, of each edit mode, of the merge patch and of the subtype.
- An authored corpus (`conformance/authored_json_edits.py`), each case with a kernel proof,
  recorded as a new corpus.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: `json_insert` that overwrites, `json_patch` that keeps a member whose patch is
  `null`, and `json_array` that quotes a JSON argument, each killed by an authored case.

## Key points

- **Files.** `Json/` (`Node.lean`, `Read.lean`, `Render.lean` with `escapeSqlText`,
  `Path.lean` with `lookupPath`), `Json/JsonApply.lean`, `Resolution/JsonFunction.lean`,
  `Resolution/Calls.lean` (`jsonFunctionNamed`, `JsonFunction.accepts`), `ExprEval.lean`,
  and the aggregates in `Resolution/ResolvedExprForm.lean` (`Aggregate`), `QueryEval.lean` and
  `Resolution/Queries.lean`.
- **Edits on the tree.** SQLite edits its JSONB blob in place (`jsonLookupStep` with
  `JEDIT_*`, `jsonCreateEditSubstructure`, `jsonMergePatch`); the model edits `JsonNode` trees
  and renders them with `renderNode`, which gives the same text. An inserted SQL value becomes
  a node as `jsonFunctionArgToBlob` makes it (text as `textraw`, numbers with their text).
- **Faults.** `malformed JSON`, `bad JSON path`, `JSON cannot hold BLOB values` and the label
  errors are `must` failures; `json_error_position` of malformed JSON is `may`.
