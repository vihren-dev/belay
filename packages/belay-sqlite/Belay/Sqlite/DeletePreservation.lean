import Belay.Sqlite.WritePreservation

set_option doc.verso true

/-! Preservation of {lit}`Conforms` by DELETE (ADR 0012, amendment 1, slice 3c): DELETE
keeps a sublist of the rows unchanged, so every kept row has a valid rowid, one cell per
column and every cell in stored form. -/

namespace Belay.Sqlite

/-- For every valid table and filter, {name}`LiteralData.deleted` is valid: DELETE keeps
a sublist of the rows unchanged. Proof sketch: the rowids of a sublist have no
duplicates, and every kept row is a row of the table. -/
theorem Table.Valid.deleted {table : Table} (valid : table.Valid) (filter : Option Resolved.Expr) :
    (LiteralData.deleted table filter).Valid := by
  refine ⟨?_, ?_⟩
  · exact (List.Sublist.map Row.rowid List.filter_sublist).nodup valid.1
  · intro row member
    exact valid.2 row (List.mem_filter.mp member).1

/-- For every profile, catalog and database, and every DELETE: if the database
{name}`Conforms` to the catalog, so does the database of its step, at every statement
position. No admission premise is needed. Proof sketch: without a table the step keeps
the database; otherwise it stores {name}`LiteralData.deleted`, which
{name}`Table.Valid.deleted` covers, with the same shape. -/
theorem literalStep_delete_conforms (conforms : Conforms profile catalog database) (position : Nat) :
    Conforms profile catalog (literalStep (.delete at_ filter returning) database position).database := by
  cases present : database at_ with
  | none => simp only [literalStep, present]; exact conforms
  | some table =>
    simp only [literalStep, present, Outcome.database]
    exact conforms.replaceRows present rfl (((conforms.2 at_).2 table present).deleted filter)

end Belay.Sqlite
