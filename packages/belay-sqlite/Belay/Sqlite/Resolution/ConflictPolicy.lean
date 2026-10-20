import Belay.Sqlite.Resolution.Catalog
import Belay.Sqlite.Resolution.ConflictForm

set_option doc.verso true

/-! The conflict algorithm of each constraint of a write. The catalog gives each key's
and each NOT NULL constraint's own algorithm, and an {lit}`INSERT OR` statement
replaces them. Resolution uses the policy to decide model restrictions, and execution
computes it again from the state's catalog. -/

namespace Belay.Sqlite

/-- The {lit}`ON CONFLICT` algorithm of the UNIQUE constraint at the position, none for a
constraint without the clause or without an entry. -/
def CatalogTable.uniqueAlgorithm (table : CatalogTable) (index : Nat) : Option ConflictAlgorithm :=
  table.uniqueAlgorithms.getD index none

/-- The algorithms of the UNIQUE constraints, one for each key of
{name}`CatalogTable.uniqueKeys`. -/
def CatalogTable.keyedUniqueAlgorithms (table : CatalogTable) : List (Option ConflictAlgorithm) :=
  table.uniqueKeys.mapIdx fun index _ => table.uniqueAlgorithm index

/-- The {lit}`ON CONFLICT` algorithm of each key of {name}`Catalog.uniqueKeys`, in its
order: the primary key's, each UNIQUE constraint's, and ABORT for each unique index. -/
def Catalog.keyAlgorithms (catalog : Catalog) (position : Nat) (table : CatalogTable) : List ConflictAlgorithm :=
  (if table.primaryKey.isEmpty then [] else [table.primaryKeyAlgorithm.getD .abort]) ++
    (table.keyedUniqueAlgorithms.map (·.getD .abort)) ++
    catalog.filterMap fun object => match object.entry with
      | .index index => if index.table == position && index.unique then some .abort else none
      | .table _ => none

/-- The algorithm of each constraint of an INSERT into the table: the statement's
{lit}`OR` algorithm when it has one (R-33948-22286), else the algorithm of the
constraint ({lit}`constraints` for the keys, {name}`CatalogColumn.notNullAlgorithm` for
NOT NULL), and ABORT for the CHECK constraints, which have no algorithm of their own. -/
def insertPolicy (table : CatalogTable) (constraints : List ConflictAlgorithm) (algorithm : Option ConflictAlgorithm) :
    Resolved.ConflictPolicy :=
  { keys := constraints.map fun own => algorithm.getD own,
    notNull := table.columns.map fun column => algorithm.getD column.notNullAlgorithm,
    check := algorithm.getD .abort }

/-- Whether the policy gives two keys different algorithms other than REPLACE, whose order
SQLite decides internally (the restriction {lit}`mixed-conflict-algorithms`). -/
def Resolved.ConflictPolicy.mixed (policy : Resolved.ConflictPolicy) : Bool :=
  (policy.keys.filter (· != .replace)).eraseDups.length > 1

/-- Whether a NOT NULL column with a default has REPLACE, which would store the default
(the restriction {lit}`replace-default`). -/
def replacesDefault (table : CatalogTable) (policy : Resolved.ConflictPolicy) : Bool :=
  (table.columns.zip policy.notNull).any fun (column, algorithm) =>
    column.notNull && column.defaultValue.isSome && algorithm == .replace

/-- Whether every algorithm of the policy is ABORT, the behavior of a plain INSERT. -/
def Resolved.ConflictPolicy.aborts (policy : Resolved.ConflictPolicy) : Bool :=
  policy.keys.all (· == .abort) && policy.notNull.all (· == .abort) && policy.check == .abort

/-- The policy of an INSERT into the table at the catalog position with the optional
{lit}`OR` algorithm: {name}`insertPolicy` over {name}`Catalog.keyAlgorithms`. Resolution
and execution both compute it from the catalog. -/
def Catalog.writePolicy (catalog : Catalog) (position : Nat) (table : CatalogTable)
    (algorithm : Option ConflictAlgorithm) : Resolved.ConflictPolicy :=
  insertPolicy table (catalog.keyAlgorithms position table) algorithm

end Belay.Sqlite
