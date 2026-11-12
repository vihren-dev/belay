import Belay.Sqlite.Model.Schema.Rows.RowEngineFacts
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyPhases

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For the given property of databases, catalog and state: the database of the state over the catalog
({name}`KeyState.database`) has the property. -/
def KeyState.Holds (invariant : Database → Prop) (catalog : Catalog) (state : KeyState) : Prop :=
  invariant (state.database catalog)

/-- For every invariant, catalog and two states with the same rows: if the second satisfies
{name}`KeyState.Holds`, the first does. Proof sketch: the database of a state reads only
its rows. -/
theorem KeyState.holds_of_rows {invariant : Database → Prop} {catalog : Catalog} {state other : KeyState}
    (rows : state.rows = other.rows) (holds : other.Holds invariant catalog) : state.Holds invariant catalog := by
  unfold KeyState.Holds KeyState.database at *
  rw [rows]
  exact holds

/-- For every catalog, state, position and table: if the database of the state has the table at
the position, the rows of the table are the rows of the state at the position. Proof sketch: the
definition of {name}`Database.table`. -/
theorem KeyState.table_rows {catalog : Catalog} {state : KeyState} {position : Nat} {table : Table}
    (found : (state.database catalog).table position = some table) : table.rows = state.rows.getD position [] := by
  obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp found
  rw [← same]
  rfl

/-- For every invariant with {name}`WriteLaws`, catalog, state, position, change of rows and table: if
the state satisfies {name}`KeyState.Holds`, the database of the state has the table at the position, and
the table with the changed rows passes the checks of a write ({name}`LiteralData.constraints` with the
unique keys of the position, and {name}`LiteralData.rowidsDistinct`), and each changed row is a row at the
position or is admitted ({name}`LiteralData.rowAdmitted`), the state after
{name}`KeyState.changeRows` satisfies {name}`KeyState.Holds`. Proof sketch: the database of the changed
state is the database after {name}`Database.setRows`, which is the write of {name}`WriteLaws`. -/
theorem KeyState.holds_write {invariant : Database → Prop} (laws : WriteLaws invariant) {catalog : Catalog}
    {state : KeyState} (holds : state.Holds invariant catalog) {position : Nat} {change : List Row → List Row}
    {table : Table} (found : (state.database catalog).table position = some table)
    (passed : (LiteralData.constraints (catalog.uniqueKeys position table.shape)
        { table with rows := change (state.rows.getD position []) } &&
      LiteralData.rowidsDistinct { table with rows := change (state.rows.getD position []) }) = true)
    (fresh : ∀ row ∈ change (state.rows.getD position []),
      row ∈ state.rows.getD position [] ∨ LiteralData.rowAdmitted table.shape row = true) :
    (state.changeRows position change).Holds invariant catalog :=
  laws.write (state.database catalog) position table _ holds found passed
    fun row member => (fresh row member).imp_left fun held => by rwa [KeyState.table_rows found]

/-- For every catalog, state, position and table: if the database of the state has the table at
the position, the catalog has the table's entry there. Proof sketch: the definition of
{name}`Database.table`. -/
theorem KeyState.table_shape {catalog : Catalog} {state : KeyState} {position : Nat} {table : Table}
    (found : (state.database catalog).table position = some table) : catalog.tableAt position = some table.shape := by
  obtain ⟨_, atShape, same⟩ := Option.map_eq_some_iff.mp found
  rw [← same]
  exact atShape

/-- For every invariant with {name}`WriteLaws`, catalog, state, position and change of rows that gives a
sublist of each list of rows: if the state satisfies {name}`KeyState.Holds`, the state after
{name}`KeyState.changeRows` satisfies it. A DELETE of a row makes such a change. Proof sketch: the database
of the changed state is the database after {name}`Database.setRows`, which is the sublist law of
{name}`WriteLaws`. -/
theorem KeyState.holds_changeRows_sublist {invariant : Database → Prop} (laws : WriteLaws invariant)
    {catalog : Catalog} {state : KeyState} (holds : state.Holds invariant catalog) {position : Nat}
    {change : List Row → List Row} (sublist : ∀ rows, (change rows).Sublist rows) :
    (state.changeRows position change).Holds invariant catalog :=
  laws.sublist (state.database catalog) position change holds sublist

/-- For every property of databases and database: if the database has the property, the state
{lit}`{ rows := database.rows }` (the rows of the database, and the default value of each other
field) satisfies {name}`KeyState.Holds` over the catalog of the database. The row engine starts
from this state. Proof sketch: the database of the state is the database. -/
theorem KeyState.holds_start {invariant : Database → Prop} {database : Database}
    (holds : invariant database) : ({ rows := database.rows } : KeyState).Holds invariant database.catalog := holds

end Belay.Sqlite.Model
