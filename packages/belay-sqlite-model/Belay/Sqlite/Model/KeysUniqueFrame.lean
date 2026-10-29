import Belay.Sqlite.Model.DatabaseConstraints
import Belay.Sqlite.Model.RowEngineFacts
import Belay.Sqlite.Model.EffectSatisfies

set_option doc.verso true

/-! Frame and row-storage lemmas for unique keys. Statement proofs use these facts with
{lit}`Effect.Satisfies Database.KeysUnique` to cover successful writes and partial FAIL writes. -/

namespace Belay.Sqlite.Model

/-- The frame lemma for one table, for every two lists of keys and two tables: if the first
table satisfies {name}`Table.KeysUnique` for the first keys, the second table has the same rows,
and each key of the second list is in the first list, then the second table satisfies
{name}`Table.KeysUnique` for the second keys. The catalog entries of the tables can differ:
the atom reads only the rows and the keys. Proof sketch: each key of the second list is a key of
the first, and the rows are the same. -/
theorem Table.KeysUnique.frame {keys kept : List UniqueKey} {table other : Table} (unique : table.KeysUnique keys)
    (rows : other.rows = table.rows) (subset : ∀ key ∈ kept, key ∈ keys) : other.KeysUnique kept :=
  fun key member => rows ▸ unique key (subset key member)

/-- The frame lemma for a table of a database, for every two databases, two positions and two
tables: if the first database satisfies {name}`Database.KeysUnique`, it has the first table at
the old position, the second table has the rows of the first, and each unique key of the new
position in the second catalog ({name}`Catalog.uniqueKeys`) is a unique key of the old position
in the first catalog, then the second table satisfies {name}`Table.KeysUnique` for the keys of
the new position in the second catalog. The second database need not have the table at the new
position; a statement that moves a table (DROP) and one that keeps it at its position use the
same lemma. Proof sketch: {name}`Table.KeysUnique.frame` of the atom at the old position. -/
theorem Database.KeysUnique.frame {before after : Database} (unique : before.KeysUnique) {position old : Nat}
    {table earlier : Table} (found : before.table old = some earlier) (rows : table.rows = earlier.rows)
    (keys : ∀ key ∈ after.catalog.uniqueKeys position table.shape, key ∈ before.catalog.uniqueKeys old earlier.shape) :
    table.KeysUnique (after.catalog.uniqueKeys position table.shape) :=
  (unique old earlier found).frame rows keys

/-- For every keys and two tables: if the first table satisfies {name}`Table.KeysUnique` for
the keys and the rows of the second are a sublist of the rows of the first, the second
satisfies it too. A DELETE stores such a sublist. Proof sketch: a pairwise property of a list
holds for each of its sublists. -/
theorem Table.KeysUnique.sublist {keys : List UniqueKey} {table other : Table} (unique : table.KeysUnique keys)
    (sublist : other.rows.Sublist table.rows) : other.KeysUnique keys :=
  fun key member => (unique key member).sublist sublist

/-- For every database, position, table and rows: if the database satisfies
{name}`Database.KeysUnique`, it has the table at the position, and the table with the rows
satisfies {name}`Table.KeysUnique` for the unique keys of the position
({name}`Catalog.uniqueKeys`), then the database after {name}`Database.setRows` with the rows at
the position satisfies {name}`Database.KeysUnique`. Proof sketch: apply {name}`Database.Every.setRows` with the fact that uses
the catalog-selected keys at each position. The general fact covers missing row lists. -/
theorem Database.KeysUnique.setRows {database : Database} (unique : database.KeysUnique) {target : Nat} {table : Table}
    (found : database.table target = some table) {rows : List Row}
    (stored : ({ table with rows } : Table).KeysUnique (database.catalog.uniqueKeys target table.shape)) :
    (database.setRows target rows).KeysUnique :=
  Database.Every.setRows (fact := fun catalog position table =>
    table.KeysUnique (catalog.uniqueKeys position table.shape)) unique found stored

end Belay.Sqlite.Model
