import Belay.Sqlite.Model.AdmittedPlainWrites

set_option doc.verso true

/-! These experiments check that the general database write facts express the
existing row-local claims. The current import direction still brings in the
specialized implementations; a production change must correct that direction. -/

namespace Belay.Sqlite.Model.ProofSimplification

/-- For every table property, database, target, table and rows: if every table
has the property, the target has the given table, and that table with the new
rows has the property, updating the target rows preserves the property on all
tables. For example, use {name}`Table.NotNull` as the property.
Proof sketch: instantiate {name}`Database.Every.setRows` with a fact that
ignores the catalog and position. -/
theorem eachTableSetRows {atom : Table → Prop} {database : Database} (every : database.EachTable atom)
    {target : Nat} {table : Table} (found : database.table target = some table) {rows : List Row}
    (stored : atom { table with rows }) : (database.setRows target rows).EachTable atom :=
  Database.Every.setRows (fact := fun _ _ table => atom table) every found stored

/-- For every database, target, table and rows: if unique keys hold in the
database, the target has the given table, and its replacement rows satisfy
the keys selected by that catalog and target, replacing those rows keeps
unique keys throughout the database. Use this for a row replacement that
keeps the catalog. It makes no claim about schema-changing statements.
Proof sketch: retain catalog and position as arguments to the fact in
{name}`Database.Every.setRows`. -/
theorem keysUniqueSetRows {database : Database} (unique : database.KeysUnique) {target : Nat} {table : Table}
    (found : database.table target = some table) {rows : List Row}
    (stored : ({ table with rows } : Table).KeysUnique (database.catalog.uniqueKeys target table.shape)) :
    (database.setRows target rows).KeysUnique :=
  Database.Every.setRows (fact := fun catalog position table =>
    table.KeysUnique (catalog.uniqueKeys position table.shape)) unique found stored

/-- For every table property, database, target, table, keys and result: assume
{name}`RowLocalAtom` evidence, the property on every existing table, the given
table at the target, and the same shape on the result. Then
{name}`checkedWrite` satisfies the property on every table. Success and the
carried database of a constraint FAIL must have it; other errors require
nothing. For example, use {name}`Table.notNullAtom` as the evidence.
Proof sketch: {name}`checkedWrite_satisfies` needs the property only after
the constraint check passes; {name}`RowLocalAtom.constraints` gives it. -/
theorem rowLocalCheckedWrite {atom : Table → Prop} (rowLocal : RowLocalAtom atom) {database : Database}
    (every : database.EachTable atom) {target : Nat} {table : Table} (found : database.table target = some table)
    (keys : List UniqueKey) (result : Table) (shape : result.shape = table.shape) :
    (checkedWrite database target keys result).Satisfies fun after => after.EachTable atom :=
  checkedWrite_satisfies every found keys result shape
    fun passed => rowLocal.constraints keys result (Bool.and_eq_true_iff.mp passed).1

/-- For every table property, database, target, table, keys, supplied rows and
result: assume {name}`RowLocalAtom` evidence, the property on every existing
table, the given table at the target, and the same shape on the result. Then
{name}`insertOutcome` satisfies the property on every table, with the same
success and constraint-FAIL cases as {name}`Effect.Satisfies`.
For example, use {name}`Table.notNullAtom` as the evidence.
Proof sketch: instantiate {name}`insertOutcome_satisfies` with the constraint
fact of the atom. -/
theorem rowLocalInsertOutcome {atom : Table → Prop} (rowLocal : RowLocalAtom atom) {database : Database}
    (every : database.EachTable atom) {target : Nat} {table : Table} (found : database.table target = some table)
    (keys : List UniqueKey) (rows : List (List Value)) (result : Table) (shape : result.shape = table.shape) :
    (insertOutcome database target keys table rows result).Satisfies fun after => after.EachTable atom :=
  insertOutcome_satisfies every found keys rows result shape
    fun passed => rowLocal.constraints keys result (Bool.and_eq_true_iff.mp passed).1

#print axioms eachTableSetRows
#print axioms keysUniqueSetRows
#print axioms rowLocalCheckedWrite
#print axioms rowLocalInsertOutcome

end Belay.Sqlite.Model.ProofSimplification
