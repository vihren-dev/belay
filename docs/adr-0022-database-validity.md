# ADR 0022: The facts of a valid database, and the statements that keep them

Date: 2026-10-22. Status: ACCEPTED on 2026-10-22 (owner decision in the design discussion of
ADR 0017's slice S2).
Implementation: slice by slice (D4), each with its own task file, as local commits.
Audience: designers and reviewers.
Related: [ADR 0012](adr-0012-query-semantics.md) (decision 5, the admitted databases),
[ADR 0016](adr-0016-model-and-surface.md) (the layer rules),
[ADR 0017](adr-0017-user-surface.md) (the user surface, D3 and D5),
ADR 0019 (proposed in pull request #207; D2, `PRAGMA integrity_check`).

## Overview

A user expects that a database satisfies the constraints of its schema: NOT NULL, CHECK, the
keys and the types of a `STRICT` table. The model's invariant `Database.Valid` does not say
this, on purpose: SQLite can reach databases whose constraints fail, and ADR 0012 admits every
database that SQLite can reach.

This ADR keeps both notions and builds them from small named facts, the atoms. A user can use
each atom alone, or a bundle of them: `Database.Valid`, the strong notion that users expect, and
`Database.Admitted`, today's weaker invariant under a new name. For each atom, a theorem says
which statements keep it. Each theorem is its own work, which the slices of D4 deliver in the
order in which the user surface needs them.

## Context

Measured on this tree on 2026-10-22:

- **Today's invariant.** `Database.Valid` (`Model/Database.lean:148`) requires a supported
  catalog (`Catalog.Valid`), one row list for each catalog object, no rows at an index's
  position, and for each table: distinct rowids, each in the signed 64-bit range, one cell for
  each column, each cell in its stored form, and the rowid in the cell of a rowid alias. Its
  docstring says: "Native representability and constraint truth are separate claims."
- **Why it is weak.** ADR 0012, decision 5: an invariant may join it "only if it holds for every
  database that SQLite can reach". Constraints can fail in such databases: after
  `PRAGMA ignore_check_constraints`, after a write to the schema with `writable_schema`, in a file
  that another program wrote, or after writes with foreign keys off.
- **The model checks the constraints already.** `LiteralData.constraints`
  (`Model/LiteralData.lean:90`) checks NOT NULL, the types of a `STRICT` table, CHECK and the
  unique keys of the catalog (`Catalog.uniqueKeys`). A write stores its result only when the
  result passes it (`checkedWrite`, `Model/StatementRun.lean:19`), and the model describes a write
  only when the table passes it before (`tableReady`). So the model does not describe a write to
  a table whose constraints fail.
- **No statement has a preservation theorem.** The model has lemmas for single operations
  (`Conforms.setRows`, `Conforms.addColumn`, `Conforms.createTable`,
  `Catalog.emptyDatabase_conforms`), not for a statement. ADR 0012 says that "a preservation
  theorem shows that the model's statements keep every invariant" (line 444); it does not exist.
- **Decidability.** `Catalog.Valid` is decidable. `Database.Valid` is not: it quantifies over
  every position and every value.
- **The user guide** ("Databases") says that each `Database` satisfies its constraints, and that
  a proof reads them with `db.notNull`, `db.check`, `db.unique` and `db.rowid_unique`.
- **ADR 0019, D2** relates the `ok` row of `PRAGMA integrity_check` to `LiteralData.constraints`,
  because `Database.Valid` does not include them.

## Decision

### D1. The atoms

Each atom is one fact about one table of a database, at its position in the catalog, or about the
whole database. Its database form says the fact for every table.

| Atom | It says | Bundle |
| --- | --- | --- |
| catalog supported | the catalog satisfies `Catalog.Valid` (database) | Admitted |
| rows shaped | one row list for each catalog object, and no rows at a position without a table (database) | Admitted |
| rowids distinct | no two rows of the table have the same rowid | Admitted |
| rowids in range | each rowid is in the signed 64-bit range | Admitted |
| rows wide | each row has one cell for each column | Admitted |
| rows stored | each cell is in the stored form of its column's affinity | Admitted |
| rows aliased | the cell of a rowid alias is the row's rowid | Admitted |
| not null | no NOT NULL column holds NULL | Valid |
| checks hold | no CHECK constraint is false for a row | Valid |
| types fit | each cell of a `STRICT` table fits its column's type | Valid |
| keys unique | no two rows conflict on a unique key of the catalog: PRIMARY KEY, UNIQUE, unique indexes with their filters, terms and collations | Valid |
| foreign keys hold | each child row matches a parent row or has a NULL in its key | neither |

Each atom has two forms: a proposition that a proof reads easily, and a check that computes,
with a lemma that the two are equivalent. The atom is decidable through its check, so `decide`
proves it for a concrete database. The checks of the constraint atoms are the functions that
the writes use (`LiteralData`), so "valid" means what the model's writes enforce. The atoms are
public in the model and named in the surface. The task file of slice 1 gives their names.

### D2. Two bundles

- **`Database.Admitted`** is today's `Database.Valid` under a new name: a structure with one
  field for each Admitted atom. It describes every database that SQLite can reach, as ADR 0012
  requires. `Conforms` becomes a fixed catalog and `Database.Admitted`.
- **`Database.Valid`** is a structure with a field for `Database.Admitted` and one field for each
  Valid atom. It describes the databases that users expect: the databases that SQLite reaches
  through statements, with no pragma or file that bypasses the constraints.

A field is an accessor: from `valid : db.Valid profile`, `valid.notNull` is the atom. Both
bundles are decidable. A claim for every database states `Database.Valid` as its hypothesis; a
claim that must hold also for databases with broken constraints states `Database.Admitted` and
the atoms that it needs.

### D3. A theorem for each atom

For each atom, a theorem says that a statement that the model describes keeps the atom. A
theorem can require a condition on the connection, for example that foreign keys are on. A
statement that can break an atom, such as `PRAGMA ignore_check_constraints` if the model
describes it, has no theorem for that atom; the theorems of the other atoms still apply to it.
A frame lemma says that a statement that does not write a table keeps every atom of that table.

The theorems are about the model's statement step (`runStatement`) and its runs (`runSql`). A
failed statement keeps the database that the model gives for it. The model refuses
`DEFERRABLE INITIALLY DEFERRED` keys today, so the foreign key atom holds after each statement
while foreign keys are on; deferred keys change the theorem when the model describes them.

A proof that fails is a finding: an error of the model, or a path through which SQLite breaks
the fact. It is reported to the owner, and no proof assumes it away.

### D4. Slices

| Slice | Content | Needed by |
| --- | --- | --- |
| 1 | the atoms, their checks, the two bundles, the rename | ADR 0017 S2: `db!` proves `Database.Valid` |
| 2 | the theorem of "keys unique" | ADR 0017 S4: a lookup by key gives at most one row |
| 3 | the theorems of the other Valid atoms | the bundled database (D5) |
| 4 | the theorems of the Admitted atoms | the bundled database (D5) |
| 5 | the theorem of "foreign keys hold" | ADR 0017 S6: the rebuild that cascades |

For the constraint atoms, a write is the easy case: `checkedWrite` stores only a result that
passes the checks. Schema statements, triggers and foreign key actions are the work. No slice
changes what a statement does, so the predictions, the claims and the judge lock do not change.

### D5. The bundled database stays open

The guide's `Database` carries its validity, so that a proof gets the facts "without extra
hypotheses". That needs `db.run` to keep `Database.Valid`, which slices 2 to 4 prove. Until then,
the surface's `Database` is the model's, and `db!` gives a proof of `Database.Valid` beside it.

A decision for later, with the bundled type: a script with a statement that has no theorem for
an atom cannot give a bundled result. Either elaboration refuses such a statement in a bundled
run, or the run gives a database with the weaker bundle.

## Consequences

- **The guide states both notions.** Its "Databases" section names the atoms, says which
  databases a claim over `Database` covers, and points to `Database.Admitted` for the others.
- **ADR 0012's preservation sentence** is corrected by an amendment that points here.
- **ADR 0019, D2** gets a simpler law: the `ok` row of `integrity_check` is the Valid constraint
  atoms, and of `quick_check` the same without "keys unique". Its text names
  `Database.Admitted` where it says `Database.Valid` today.
- **The work is a matrix** of atoms and statement forms, which the slices deliver one atom at a
  time, so each slice is useful alone.

## Alternatives considered

**One strong invariant without atoms.** Rejected: one statement that bypasses a constraint would
lose every fact, and the user could not use the facts that still hold. A helper must never be
the only door (the workspace rule on flexibility and usability).

**Add the constraints to today's invariant.** Rejected: claims would then silently exclude
databases that SQLite can reach, against ADR 0012's rule.

**Bundle the surface's database in S2.** Rejected: `db.run` cannot give the proof before the
theorems of D3 exist.

## Not decided here

- The bundled database (D5) and how a run treats a statement without a theorem.
- Whether the cells of stored generated columns become an atom.
- The model of `PRAGMA ignore_check_constraints` and `writable_schema`.

## Owner decisions

Decided on 2026-10-22, in the design discussion of S2:

1. **The atoms are the primitives**, public, and the two bundles are built from them.
2. **Strong is `Database.Valid`, weak is `Database.Admitted`.**
3. **Foreign keys are an atom outside `Database.Valid`.**
4. **A theorem for each atom**, with conditions on the connection, delivered slice by slice; the
   postponed work is documented, and the guide keeps its scope.
