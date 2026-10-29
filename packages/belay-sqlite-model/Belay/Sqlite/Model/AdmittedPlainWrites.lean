import Belay.Sqlite.Model.AddColumnFromValid
import Belay.Sqlite.Model.DatabaseFactChecks
import Belay.Sqlite.Model.TableAtomWrites
import Belay.Sqlite.Model.StatementStep

set_option doc.verso true

/-! Constraint and catalog facts for the admitted table atoms. The general plain-write
proofs live in {lit}`TableAtomWrites`, below these invariant instances. -/

namespace Belay.Sqlite.Model

/-- For every table and keys: if the table passed the check of {name}`checkedWrite`, its rowids are
distinct. Proof sketch: the check contains {name}`LiteralData.rowidsDistinct`, which agrees with
{name}`Table.RowidsDistinct`. -/
theorem passed_rowidsDistinct {keys : List UniqueKey} {table : Table}
    (passed : (LiteralData.constraints keys table && LiteralData.rowidsDistinct table) = true) :
    table.RowidsDistinct :=
  (Table.rowidsDistinct_iff table).mp (Bool.and_eq_true_iff.mp passed).2

/-- For every limits, database with a valid catalog, target and table at the target: the column of the
rowid alias of the table, if there is one, is not generated. Proof sketch: a supported table has that fact
({name}`CatalogTable.SupportedFacts`). -/
theorem Database.aliasUngenerated {limits : Limits} {database : Database} (valid : database.catalog.Valid limits)
    {target : Nat} {table : Table} (found : database.table target = some table) :
    ∀ position, table.shape.rowidAlias = some position →
      ∃ column, table.shape.columns[position]? = some column ∧ column.generated = none := by
  obtain ⟨_, _, _, _, _, _, alias, _⟩ := (CatalogTable.supported_iff _ _).mp
    (valid.tableSupported (Database.tableAt_of_table found))
  intro position same
  obtain ⟨_, _, column, atColumn, ungenerated, _⟩ := alias position same
  exact ⟨column, atColumn, ungenerated⟩

end Belay.Sqlite.Model
