# Status: index forms (ADR 0014, slice 1)

Created 2026-10-19. Status: open.
Task file: [task](20261019-index-forms.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D1.

## Relevant files

- Syntax and frontend: `packages/belay-sqlite/Belay/Sqlite/Resolution/Syntax.lean`,
  `belay/sqlite/syntax_definitions.py`.
- Catalog and keys: `Resolution/Catalog.lean`, `LiteralData.lean`, `Upsert.lean`,
  `RowUpdate.lean`, `Resolution/Upserts.lean`, `Resolution/ConflictPolicy.lean`.
- Resolution and execution: `Resolution/Definitions.lean`, `Execution.lean`,
  `StatementStep.lean`.
- Harness: `packages/verifier-conformance/VerifierConformance/Native.lean`,
  `Predict.lean`, `conformance/native_metadata.py`, `conformance/predict_render.py`.

## Progress

- 2026-10-19: native behaviour of index forms checked with 3.51.0 (prepare errors of
  terms and filters, `date('now')` refused only when a row is written, a string term read
  as a column, partial unique indexes over existing rows). The judge compares partial
  indexes, expression keys and sort orders already, so no judge change.

- 2026-10-19: outcomes 1 to 6 in one commit. Syntax `createIndex` has key terms
  (`OrderTerm`) and a filter, mapped by `belay/sqlite/syntax_indexes.py`; the record is
  version 4. `Resolution/Keys.lean` has `KeyTerm`, `IndexKey`, `CatalogIndex` and
  `UniqueKey`; `Catalog.uniqueKeys` gives every key in one form, and
  `LiteralData.keyEqual` evaluates terms at clock 0 and the filter (`keyApplies`).
  `Resolution/IndexTerms.lean` resolves terms and filters with SQLite's prepare errors
  (`qualifiedIndexTerm`, `nondeterministicIndex`) and the restrictions
  `index-string-term`, `index-date-function` and `index-json-function`;
  `create-index-runs` is gone, and `step` builds an index over existing rows.
  `Resolved.Expr.readsBelow` exists once (`ExprAny.lean`). The harness's `NativeIndex`
  has expression keys, sort orders and the partial flag, written only when present, so
  the frozen model cases keep their form; the two frozen cases with CREATE INDEX get the
  new Syntax, as step 1 of ADR 0013 did. Authored corpus `authored_indexes` (20 cases,
  corpus version 29) and `index_mutants` (three mutants). The core has 134 modules.

- 2026-10-19: checks. Fixes after the first suite runs: tests read record version 4; the
  index corpus records no clock (the two time cases moved to the Lean examples); an index
  may repeat a column, as SQLite allows; the boundary and requirement tests expect the
  CREATE INDEX cases that now agree; the frozen index cases keep their quoted key names.
  `just test-full`, `just test-nix` and `just test-scheduled` pass. Verdict: 112 upstream
  cases newly agree (v1 +2, v2 +2, v3 +7, v4 +23, v5 +78), none leaves AGREE; corpus 29
  (20 cases) agrees in full. Freed 18 GiB of old `/tmp/nix-shell.*` directories with the
  owner's approval for the disk guard.

## Remaining

- CI time, pull requests A and B.
