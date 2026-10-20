# Status: `STRICT` tables (ADR 0014, slice 6)

Created 2026-10-20. Status: DONE (pull requests #189 and #190).
Task file: [task](20261020-strict-tables.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D6.

## Progress

- 2026-10-20: native behaviour checked with 3.51.0: the allowed types, with ASCII case
  ignored, and the two prepare errors; `cannot store TEXT value in INTEGER column s.a` with
  extended code 3091 after affinity; NOT NULL first, then the type, then CHECK; every
  `OR` algorithm acts as ABORT (corrected later the same day: `OR FAIL` keeps no earlier
  row and `OR ROLLBACK` keeps the transaction open); generated columns and `DO UPDATE` are checked; `ANY` keeps text as text; a rowid
  alias still gives `datatype mismatch`; ADD COLUMN with an unknown type fails at step.

- 2026-10-20: the model, the frontend and the tests (commit "STRICT tables").
  - Frontend `table_options` reads `STRICT`; Lean `Resolution/StrictTypes.lean`,
    `CatalogColumn.strictType`, `CatalogTable.strict`, `definedColumn` (the strict type
    before affinity and DEFAULT), `strictTypeError`, `typesFit` in `constraints` and
    `upsertRow` (ABORT), `strictDefaultFits` and the restriction `add-column-strict-type`.
  - The harness gives ADD COLUMN to a `STRICT` table the `pragma_quick_check` output column.
  - `Resolution/StrictExamples.lean`; `conformance/authored_strict.py` (25 cases, all
    agree with kernel proofs), `strict_evidence.py` (corpus 34), `strict_mutants.py`
    (three mutants, all killed); the CHECK mutants follow the new step of `upsertRow`.

- 2026-10-20: review of "STRICT tables": a must finding, the implicit NOT NULL of the
  primary-key columns of a `STRICT` table, and three file-length findings. Fixed in
  "refactor: NOT NULL keys of STRICT tables": `Resolution/TableOptions.lean`
  (`CatalogTable.withStrictKeys`, with `asWithoutRowid`, `definedColumn` and
  `strictTypeError` moved from `Definitions.lean`), three more authored cases (28),
  `tests/syntax_table_options_test.py`.

- 2026-10-20: `just test-full`, `just test-nix` and `just test-scheduled` pass. CI time
  with forced rebuilds: harness 22 s, model 407 s, frozen 142 s, mutants 623 s. Verdict:
  10 upstream cases newly agree (`alter-20.1` and `alter-20.3` in v1 to v5), none leave
  AGREE, and corpus 34 has 28 AGREE. Claims and lock in "claims: corpus 34 ...". Pull
  requests #189 (A) and #190 (B).

## Remaining

- None. DONE.
