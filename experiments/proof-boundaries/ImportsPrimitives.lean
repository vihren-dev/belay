import Belay.Sqlite.Model.Comparison
import Belay.Sqlite.Model.AdmittedCellLaws
import Belay.Sqlite.Model.DatabaseFacts
import Belay.Sqlite.Model.Resolution.CatalogSpec

set_option doc.verso true

namespace ProofBoundaries
open Belay.Sqlite.Model

/-- BINARY-equal values compare equal under every built-in collation. This is
the existing FK-owned proof with foundational imports only. Proof sketch:
equal ranks and byte strings settle text; other values keep BINARY comparison. -/
theorem compare_eq_of_binary {first second : Value} (equal : Value.compare first second = .eq)
    (collation : Collation) : collation.compare first second = .eq := by
  have parts := equal
  simp only [Value.compare, compareLex_eq_eq, compareOn] at parts
  have ranks : first.rank = second.rank := Std.LawfulEqCmp.eq_of_compare parts.1
  have bytes : first.bytes = second.bytes := Std.LawfulEqCmp.eq_of_compare parts.2.2
  cases first <;> cases second <;> cases collation <;>
    simp only [Collation.compare, Collation.key] <;> try exact equal
  all_goals simp_all [Value.rank, Value.bytes]
  all_goals first
    | exact Std.ReflCmp.compare_self (cmp := Value.compare)
    | have impossible := parts.1
      split at impossible <;> contradiction

/-- With no generated column, generated-cell evaluation keeps the entire cell
list. Proof sketch: the existing generic invariant has no possible update. -/
theorem generated_cells_plain (columns : List CatalogColumn) (values : List Value)
    (plain : ∀ column ∈ columns, column.generated = none) :
    LiteralData.generatedCells columns values = values := by
  apply LiteralData.generatedCells_invariant (fun cells => cells = values) rfl
  intro cells position column value found generated _
  simp [plain column (List.mem_of_getElem? found)] at generated

/-- A database table lookup gives its shape in the catalog at the same position.
Proof sketch: the table is the map of that catalog lookup. -/
theorem table_at_of_table {database : Database} {target : Nat} {table : Table}
    (present : database.table target = some table) : database.catalog.tableAt target = some table.shape := by
  unfold Database.table at present
  cases found : database.catalog.tableAt target with
  | none => simp [found] at present
  | some shape => simp [found] at present; rw [← present]

/-- A named catalog table gives a database table with exactly its stored rows.
Proof sketch: the catalog name lookup supplies the object at that position. -/
theorem table_of_find_table (database : Database) (name : Identifier) (position : Nat) (shape : CatalogTable)
    (found : database.catalog.findTable name = some (position, shape)) :
    database.table position = some { shape, rows := database.rows.getD position [] } := by
  obtain ⟨⟨objectName, objectEntry⟩, atPosition, entry, -⟩ := Catalog.findTable_some _ _ _ _ found
  cases entry
  simp [Database.table, Catalog.tableAt, atPosition]

end ProofBoundaries

#print axioms ProofBoundaries.compare_eq_of_binary
#print axioms ProofBoundaries.generated_cells_plain
#print axioms ProofBoundaries.table_at_of_table
#print axioms ProofBoundaries.table_of_find_table
