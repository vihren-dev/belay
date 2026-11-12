import Belay.Sqlite.Model.Resolution

set_option doc.verso true

/-! Where each unique key of a table comes from, and which of several keys that fail SQLite
names. SQLite 3.51 checks the keys of a row in this order (measured with the {lit}`sqlite3`
shell):

* the rowid alias (an {lit}`INTEGER PRIMARY KEY`);
* the indexes of {lit}`CREATE UNIQUE INDEX`, the newest first;
* the PRIMARY KEY and UNIQUE constraints of {lit}`CREATE TABLE`, in the reverse of their written
  order;
* the keys declared {lit}`ON CONFLICT REPLACE` after all others, also when the statement's
  algorithm overrides REPLACE. The rowid alias is the exception: declared REPLACE, it comes
  after all others only when REPLACE applies; with {lit}`INSERT OR FAIL` or {lit}`INSERT OR ABORT`
  it comes first. For {lit}`ip(id INTEGER PRIMARY KEY ON CONFLICT REPLACE, u UNIQUE)`, a plain
  INSERT that repeats both names {lit}`ip.u`, and {lit}`INSERT OR FAIL` names {lit}`ip.id`.

The catalog does not keep the place of a PRIMARY KEY that is not the rowid alias among the UNIQUE
constraints, so for such a key the choice has two candidates. -/

namespace Belay.Sqlite.Model

/-- Where a unique key of a table comes from. For example, the second UNIQUE constraint of a
table is {lean}`KeySource.unique 1`. -/
inductive KeySource where
  /-- The PRIMARY KEY of the table. -/
  | primaryKey
  /-- The UNIQUE constraint at the position, in written order ({name}`CatalogTable.uniqueKeys`). -/
  | unique (written : Nat)
  /-- The unique index at the catalog position. -/
  | index (position : Nat)
  deriving Repr, DecidableEq

/-- The source of a catalog object at its position, when it is a unique index on the table at
{lit}`table`; none for every other object. -/
def indexSource (table : Nat) : CatalogObject × Nat → Option KeySource
  | ({ entry := .index index, .. }, place) => if index.table == table && index.unique then some (.index place) else none
  | ({ entry := .table _, .. }, _) | ({ entry := .view _, .. }, _) | ({ entry := .trigger _, .. }, _) => none

/-- The source of each key of {name}`Catalog.uniqueKeys` of the table at the position, in the
same order: the PRIMARY KEY when there is one, the UNIQUE constraints, and the unique indexes on
the table in catalog order. -/
def Catalog.keySources (catalog : Catalog) (position : Nat) (table : CatalogTable) : List KeySource :=
  (if table.primaryKey.isEmpty then [] else [.primaryKey]) ++ (List.range table.uniqueKeys.length).map .unique ++
    catalog.zipIdx.filterMap (indexSource position)

/-- For every catalog, position and table: {name}`Catalog.keySources` has as many entries as
{name}`Catalog.uniqueKeys`, so the key at each position has its source at the same position.
Proof sketch: the two lists are built from the same three parts; for the indexes, induction over
the catalog. -/
theorem Catalog.keySources_length (catalog : Catalog) (position : Nat) (table : CatalogTable) :
    (catalog.keySources position table).length = (catalog.uniqueKeys position table).length := by
  simp only [Catalog.keySources, Catalog.uniqueKeys, List.length_append, List.length_map, List.length_range]
  congr 1
  · split <;> simp
  · suffices ∀ start, ((catalog.zipIdx start).filterMap (indexSource position)).length =
        (catalog.filterMap fun object => match object.entry with
          | .index index => if index.table == position && index.unique then some index.uniqueKey else none
          | .table _ | .view _ | .trigger _ => none).length from this 0
    induction catalog with
    | nil => simp
    | cons object rest restLength =>
      intro start
      rcases object with ⟨name, entry⟩
      cases entry with
      | index index =>
        by_cases unique : index.table = position ∧ index.unique = true <;>
          simp [List.zipIdx_cons, indexSource, restLength, unique]
      | table _ | view _ | trigger _ => simp [List.zipIdx_cons, List.filterMap_cons, indexSource, restLength]

/-- Whether the table declares the key of the source {lit}`ON CONFLICT REPLACE`. A unique index
has no such clause. -/
def CatalogTable.declaredReplace (table : CatalogTable) : KeySource → Bool
  | .primaryKey => table.primaryKeyAlgorithm == some .replace
  | .unique written => (table.uniqueAlgorithms[written]?).join == some .replace
  | .index _ => false

/-- The keys, among the failing positions of one group, that SQLite may name: the newest failing
unique index when one fails; otherwise the last failing UNIQUE constraint in written order and
the failing PRIMARY KEY, whose place among them the catalog does not keep. -/
def pickKeys (sources : List KeySource) (group : List Nat) : List Nat :=
  match (group.filter fun index => sources[index]? matches some (.index _)).getLast? with
  | some newest => [newest]
  | none => ((group.filter fun index => sources[index]? matches some (.unique _)).getLast?).toList ++
      group.filter fun index => sources[index]? == some .primaryKey

/-- The positions of the failing keys (in {name}`Catalog.uniqueKeys`) that SQLite may name for
one row, from their sources ({name}`Catalog.keySources`):

* the PRIMARY KEY alone when the table has a rowid alias and the PRIMARY KEY fails;
* otherwise {name}`pickKeys` of the keys that the table does not declare REPLACE
  ({name}`CatalogTable.declaredReplace`), and when none of them fails, of the REPLACE keys.

For example, for a table {lit}`(a UNIQUE, b UNIQUE)` whose keys both fail, it is
{assert}`keyCandidates [.unique 0, .unique 1] { columns := [] } [0, 1] = [1]`. -/
def keyCandidates (sources : List KeySource) (table : CatalogTable) (failing : List Nat) : List Nat :=
  let primary := failing.filter fun index => sources[index]? == some .primaryKey
  if table.rowidAlias.isSome && !primary.isEmpty then primary else
  match pickKeys sources (failing.filter fun index => !(sources[index]?.any table.declaredReplace)) with
  | [] => pickKeys sources (failing.filter fun index => sources[index]?.any table.declaredReplace)
  | chosen@(_ :: _) => chosen

end Belay.Sqlite.Model
