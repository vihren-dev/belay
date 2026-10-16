# Rowid aliases, slice 5b of ADR 0012

Created 2026-10-15. Status: DONE (pull requests #134 and B).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Amendment 4: Unique keys
and conflicts (slices 5a to 5d)", "Rowid aliases (slice 5b)", with the owner decisions of
2026-10-15 (#131). Related: slice 5a ([task](20261015-key-values.task.md)); slices 5c and
5d (conflicts) follow this slice.

## Pull requests

- **Pull request A (subject):** catalog support, execution, invariants, proofs, error
  mapping, restriction registry changes, examples, authored coverage cases, mutants and a
  corpus writer. No change under `judge/` or `integrity/`.
- **Pull request B (judge, owner approval):** the coverage corpus (version 18) is frozen
  and claimed, and cases that newly agree are added to `mustAgree`.

## Outcome

1. **Form.** A table of the schema whose single-column `PRIMARY KEY` is a column declared
   `INTEGER` (any case), as a column or a table constraint, and not `DESC`, has that
   column as a rowid alias (`aliasesRowid`). `INT PRIMARY KEY` and
   `INTEGER PRIMARY KEY DESC` are not aliases. Such tables are admitted: `Conforms`
   requires, for every row, that the alias cell is the integer rowid of the row, which
   SQLite guarantees. `CREATE TABLE` with constraints in a migration stays the
   restriction `create-table-constraints`.
2. **INSERT.** For each row, in order: a NULL or omitted alias value gives the next rowid
   (`nextRowid`), also with `NOT NULL` on the alias; another value is stored with INTEGER
   affinity and must then be an integer (`' 7 '` and `'8.0'` store `7` and `8`), else the
   statement fails with SQLite's `datatype mismatch` (`SQLITE_MISMATCH`, primary code 20),
   as for `'0x10'`, `1.5`, `1e20` and a BLOB. The row's rowid is the alias value. A
   duplicate is the unique-key failure of today. `RETURNING` reads the alias.
3. **UPDATE.** Assigning the alias moves the row to the new rowid: NULL and a value that
   is not an integer after INTEGER affinity are `datatype mismatch`; a duplicate is the
   unique-key failure. A `SET` value that reads the row for the alias stays the restriction
   `row-dependent-key`.
4. **Errors and atomicity.** `datatype mismatch` is a statement failure with the database
   unchanged, as ABORT. The model records it in traces and outputs with its phase (step).
5. **Restrictions.** `rowid-alias` leaves the registry, its documentation and its
   examples. The rowid names (`rowid-name`) and the random rowid after the largest one (the
   bounded-rowid obligation) stay.
6. **Verification target.** `Contract.lean` does not change; `Conforms` gains the alias
   invariant, and every write keeps it.
7. **Evidence.** Authored coverage cases agree with native SQLite and have kernel proofs;
   each mutant below changes a verdict; the verdict counts of the claimed corpora do not
   go down.

## Tests

- Lean examples: alias detection for each declaration form; INSERT with NULL, omitted,
  integer, text and real alias values; `datatype mismatch`; UPDATE of the alias; the next
  rowid after explicit aliases.
- Proofs: every INSERT and UPDATE keeps `Conforms` with the alias invariant; for a table
  without an alias, INSERT and UPDATE keep their current semantics.
- Authored coverage cases: each declaration form (column and table constraint, lower case,
  `NOT NULL`, `DESC` and `INT` as non-aliases); INSERT of NULL, omitted, negative,
  explicit, `' 7 '` and `'8.0'` aliases, and of `'0x10'`, `1.5`, `1e20` and a BLOB
  (mismatch); a duplicate alias; the next rowid after an explicit alias; `RETURNING` of
  the alias; UPDATE of the alias to a new value, a duplicate, NULL and text; a query that
  reads the alias in `WHERE` and `ORDER BY`.
- Mutants, each changing the verdict of an authored case: NULL alias stored as NULL
  instead of the next rowid; a non-integer alias stored instead of the mismatch error;
  the rowid kept instead of the alias value; UPDATE of the alias without moving the
  rowid; `DESC` treated as an alias.
- The restriction registry, example, documentation and mutant link tests after the
  restriction leaves.

## Key points for the implementer

- **Admission.** `CatalogTable.supported` (`Model.lean`) and `CatalogTable.plain`
  (`Execution.lean`) exclude aliases; `Resolution/Definitions.lean` detects them
  (`aliasesRowid`, `rowidAlias`) and refuses writes to such tables (`.rowidAlias`).
- **Rows.** `Row` (`Declarations.lean`) is a rowid and the cells; the alias is one of the
  cells. `LiteralData.insertRow` and `nextRowid`, and `RowUpdate.assign`, build rows;
  `Table.Valid` (`Model.lean`) states the row invariants and is where the alias invariant
  belongs. The preservation proofs (`LiteralPreservation.lean`, `WritePreservation.lean`,
  `Preservation.lean`) use `Table.Valid`.
- **Errors.** `ExecutionError` (`Execution.lean`) has no mismatch; the conformance mapping of
  errors to result codes and phases is in `packages/verifier-conformance/VerifierConformance/Case.lean`.
- **Uniqueness.** The alias is the table's primary key, so the key check of slice 5a already
  finds a duplicate alias; the rowids of an admitted table are then distinct.
- **Native records.** Native snapshots record the rowid and the cells separately; check that
  an alias table's snapshot gives both as the model expects.
- **Kernel and mutant cost.** Keep authored cases small; measure the mutant and model suites
  after the change.
