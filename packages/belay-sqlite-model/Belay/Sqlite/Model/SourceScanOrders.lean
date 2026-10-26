import Belay.Sqlite.Model.QueryEval
import Belay.Sqlite.Model.Resolution.Keys
import Belay.Sqlite.Model.Database

set_option doc.verso true

/-! The orders in which SQLite may read the rows of one table for the source of an INSERT (ADR 0019,
D4, amended 2026-10-25). A scan without an index reads the rows by rowid, or by primary key for a
{lit}`WITHOUT ROWID` table; a plan that uses an index reads them in the order of the index entries,
which is the key order and then the order of the scan. The model's own run reads the scan order. Another
order can change the rowids that an INSERT assigns, the row that a conflict keeps, the row at which a
source error stops the statement, and {lit}`last_insert_rowid()`. -/

namespace Belay.Sqlite.Model

/-- The key terms of every index that SQLite may read a table by, besides its scan: the keys of the
{lit}`PRIMARY KEY` and {lit}`UNIQUE` constraints, which SQLite keeps as indexes, and each index of
the catalog on the table, with its filter when it is a partial index. -/
def Catalog.accessKeys (catalog : Catalog) (position : Nat) (shape : CatalogTable) :
    List (List IndexKey × Option Resolved.Expr) :=
  ((if shape.primaryKey.isEmpty then [] else [shape.primaryKey]) ++ shape.uniqueKeys).map
      (fun positions => ((UniqueKey.ofColumns shape.columns positions).terms, none)) ++
    catalog.filterMap fun object => match object.entry with
      | .index index => if index.table == position then some (index.keys, index.filter) else none
      | .table _ | .view _ | .trigger _ => none

/-- The value of a key term over the values of a row. -/
def IndexKey.valueOf (key : IndexKey) (values : List Value) : Value :=
  match key.term with
  | .column position => values.getD position .null
  | .expression expression => expression.eval (Resolved.EvalContext.plain 0) values

/-- The rows in the order of an index: the rows that its filter keeps, stably sorted by the key terms,
each under its direction and collation, and then the other rows in scan order. A partial index
holds only the first group, and SQLite reads it only when no row that it needs is in the second, so
the order of the second group is never read for a needed row. -/
def Table.indexOrder (rows : List Row) (keys : List IndexKey) (filter : Option Resolved.Expr) : List Row :=
  let held := rows.filter fun row => filter.all fun condition =>
    Resolved.truthy (condition.eval (Resolved.EvalContext.plain 0) row.values)
  let directions := keys.map fun key => (key.descending, key.collation)
  let sorted := Resolved.stableSort
    (fun a b => (Resolved.compareSort directions (keys.map (·.valueOf a.values)) (keys.map (·.valueOf b.values))).isLE) held
  sorted ++ rows.filter fun row => !(held.any (·.rowid == row.rowid))

/-- The orders in which SQLite may read the rows of the table at the position, each once: the scan
order first, which is the order of the model's own run ({name}`Belay.Sqlite.Model.Table.scanRows`),
then the order of each index ({name}`Catalog.accessKeys`, {name}`Table.indexOrder`) that differs from
the orders before it. -/
def Table.accessOrders (catalog : Catalog) (position : Nat) (table : Table) : List (List Row) :=
  let scan := table.scanRows
  (scan :: (catalog.accessKeys position table.shape).map fun (keys, filter) => Table.indexOrder scan keys filter).foldl
    (fun found order => if found.any (fun other => other.map (·.rowid) == order.map (·.rowid)) then found else found ++ [order]) []

end Belay.Sqlite.Model
