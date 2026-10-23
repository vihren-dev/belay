# The facts of a valid database (ADR 0022, slice 1)

Created 2026-10-22. Status: DONE (2026-10-22).
Status file: [status](20261022-validity-atoms.status.md).
Specification: [ADR 0022](../docs/adr-0022-database-validity.md), D1, D2 and D4 (slice 1).
Needed by: S2 of the user surface ([ADR 0017](../docs/adr-0017-user-surface.md), D3, amended
2026-10-22), whose `db!` proves `Database.Valid`.

## Scope

The model gets the atoms of ADR 0022, D1, each with a proposition, a check and the lemma that
they are equivalent; the two bundles of D2; and the rename of today's invariant to
`Database.Admitted`. Nothing that a statement does changes.

Out of scope: the theorems that statements keep the atoms (slices 2 to 5); a `Database` type
that carries its validity (ADR 0022, D5); the surface.

## Outcome

1. **The atoms.** For each atom of ADR 0022, D1, the model has:
   - a proposition for one table, at its position in the catalog (or for the whole database,
     for the two database atoms), which a proof reads without unfolding a check;
   - its database form, for every table;
   - a check that computes, with a lemma that the check is `true` exactly when the proposition
     holds, and a `Decidable` instance through the check, so that `decide +kernel` proves the
     atom, or its negation, for a concrete database.

   The checks of "not null", "checks hold", "types fit" and "keys unique" are the functions that
   the writes use, and `LiteralData.constraints` is built from them, so that one definition of
   each constraint exists. "Keys unique" uses the keys of the catalog (`Catalog.uniqueKeys`).
   "Foreign keys hold" uses the matching of `ForeignKeyMatch` for every foreign key of the
   catalog, deferred or not.
2. **`Database.Admitted`.** A structure, one field for each Admitted atom, with the meaning of
   today's `Database.Valid`. `Conforms` uses it. The lemmas over `Conforms`
   (`Catalog.emptyDatabase_conforms`, `Conforms.shape`, `Conforms.table`, `Conforms.setRows`,
   `Conforms.addColumn`, `Conforms.createTable`) keep their statements.
3. **`Database.Valid`.** A structure with the field `admitted` and one field for each Valid atom.
   Its fields, or definitions over them, have the guide's names: `notNull`, `check`, `unique` and
   `rowid_unique`. "Foreign keys hold" is `Database.ForeignKeysHold`, outside both bundles.
4. **Both bundles are decidable**, through the checks of their atoms.
5. **The root imports them.** `Belay.Sqlite.Model` imports the new modules, so that the surface
   can use them (ADR 0016, D2).
6. **The old name is gone.** No definition named `Database.Valid` with today's meaning remains,
   and the docs, the tests and the docstrings that name today's invariant say
   `Database.Admitted`.

## Tests

- **An example for each atom.** A Lean file of examples gives, for each atom, a database on which
  it holds and one on which it fails, both proved with `decide +kernel`. The failing cases
  include: a NULL in a NOT NULL column, a CHECK that is false, a text in a `STRICT INTEGER`
  column, two rows equal on a UNIQUE column, two rows equal on a partial unique index whose filter
  is true for both, two texts equal under `NOCASE` on a unique index with that collation, two equal rowids, a rowid out of range, a short row, a cell
  not in its stored form, an alias cell that is not the rowid, a child row without a parent.
- **Cases that hold although they look like failures.** Two rows equal on a partial unique index
  whose filter is false for one of them, and two rows with NULL in the same UNIQUE column: SQLite
  stores both, and "keys unique" holds (`LiteralData.keyEqual`).
- **The bundles.** `decide +kernel` proves `Database.Valid` for the guide's first example
  database (the table `invoices` with two rows), and proves for a database with a NULL in a NOT
  NULL column that it is `Database.Admitted` and not `Database.Valid`.
- **The lemmas.** The equivalence lemmas and the restated `Conforms` lemmas compile; the
  existing tests that use `Conforms` (`tests/shared_table_shape_test.py`,
  `tests/test_model_package.py`, `tests/test_model_ownership.py`) pass.
- **No change of behavior.** The predictions of every frozen corpus are byte-identical to those
  before the task (`nix-build integrity/judge.nix -A predictions`, then `diff -r`).
- **The usual checks.** The model's suites, the documentation inventory and `just test-full`.

## Key points

- **Decidability.** Today's `Database.Valid` quantifies over every position and every value, so
  it is not decidable. The checks iterate over the catalog's positions and the rows; the
  equivalence lemmas carry the quantifiers. Positions after the catalog hold no table
  (`Database.table`).
- **Kernel reduction.** `decide +kernel` must reduce the checks. Avoid well-founded recursion in
  them, as the existing `LiteralData` functions do.
- **One definition of each constraint.** If an atom had its own check beside
  `LiteralData.constraints`, the two could disagree, and "valid" would no longer mean what the
  writes enforce. Restate `constraints` over the atoms' checks, and keep its lemmas
  (`LiteralData.insertRow_constraints`, `uniqueRows_append`).
- **Rows and cells.** `LiteralData.constraints` checks NOT NULL over zipped column and cell
  pairs, so a short row passes it; "rows wide" is the atom that excludes short rows. Keep that
  split: each atom states one fact.
- **Plain words.** Each new proposition and each field of type `Prop` gets a docstring that
  restates it in plain words (`CLAUDE.md`, "Propositions in plain words"), with Verso
  references.
- **The rename touches** `Model/Database.lean`, `ModelLaws.lean`, `SchemaExtensionLaws.lean`,
  `DatabaseWriteLaws.lean`, `StoreValueLaws.lean`, the three tests above and the docs that name
  `Database.Valid` (`docs/semantic-subset.md` and others). Historical ADR text keeps the old name;
  ADR 0019 (pull request #207) is outside this tree, and its D2 names the new atoms when it lands.
- **Files under 200 lines.** The atoms need more than one module; the examples go in their own
  file, outside the root's import closure, as the other `*Examples.lean` files are.
