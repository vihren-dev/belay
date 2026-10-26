import Belay.Sqlite.Model.ForeignKeyFacts

set_option doc.verso true

/-! Frame laws for row-reference validity. Each surviving child declaration keeps the parent
definition and rows that its supplied comparison reads. -/

namespace Belay.Sqlite.Model

/-- For a located parent target, the transported position has the same parent-column definitions
and stored rows in the two databases. Missing and mismatched targets require nothing because
their comparisons find no parent. Supporting indexes are not read. -/
def ParentLink.RowFrame (move : Nat → Nat) (before after : Database) : ParentLink → Prop
  | .located position _ =>
    (after.catalog.tableAt (move position)).map (·.columns) = (before.catalog.tableAt position).map (·.columns) ∧
      after.rowsAt (move position) = before.rowsAt position
  | .missing | .mismatch _ => True

/-- For every pair of databases, parent link, child key and row, transporting the link keeps
satisfaction equal when its parent-column definitions and rows agree. Child positions do not
affect a row comparison. Proof sketch: missing targets use only the original NULL test;
located targets use the same rowid or column comparison on equal parent data. -/
theorem ForeignKeyLink.satisfied_transport (before after : Database) (move : Nat → Nat)
    (link : ForeignKeyLink) (child : Nat) (row : Row) (frame : link.parent.RowFrame move before after) :
    ({ link with child, parent := link.parent.transport move }).satisfied after row =
      link.satisfied before row := by
  rcases link with ⟨oldChild, declaration, parent⟩
  cases parent with
  | missing => rfl
  | mismatch _ => rfl
  | located position key =>
    obtain ⟨columns, rows⟩ := frame
    cases oldShape : before.catalog.tableAt position <;>
      cases newShape : after.catalog.tableAt (move position) <;>
      simp only [oldShape, newShape, Option.map_none, Option.map_some, Option.some.injEq] at columns
    all_goals try contradiction
    · cases key <;> simp [ForeignKeyLink.satisfied, ParentLink.transport, oldShape, newShape,
        ForeignKeyLink.hasNull, childValues, childPositions]
    · simp only [ForeignKeyLink.satisfied, ParentLink.transport, oldShape, newShape, rows]
      cases key <;> simp only [parentFound, childValues, childPositions, ForeignKeyLink.hasNull]
      congr 3
      funext candidate
      simp only [indexHolds, columns]

/-- The input dependencies for carrying a table's row-reference fact to another table:
every new declaration and row already occurs in the old table; each new mapping is the
transported old mapping; and every located parent retains its columns and rows. Empty new
tables need no row correspondence, but declarations and mappings are still compared. -/
structure Table.RowReferenceFrame (before after : Database) (oldMapping newMapping : ForeignKeyMapping)
    (move : Nat → Nat) (oldPosition position : Nat) (oldTable table : Table) : Prop where
  /-- Each new declaration already occurs in the old table. -/
  declarations : ∀ key ∈ table.shape.allForeignKeys, key ∈ oldTable.shape.allForeignKeys
  /-- Each new stored row already occurs in the old table. -/
  rows : ∀ row ∈ table.rows, row ∈ oldTable.rows
  /-- Every new declared mapping is the old mapping with its parent position transported. -/
  mapping : ∀ key ∈ table.shape.allForeignKeys,
    newMapping.parent position key = (oldMapping.parent oldPosition key).transport move
  /-- Every located parent read by a new declaration retains its columns and stored rows. -/
  parents : ∀ key ∈ table.shape.allForeignKeys,
    (oldMapping.parent oldPosition key).RowFrame move before after

/-- For every table row-reference fact and frame, the target table has the row-reference fact
under the new mapping. Proof sketch: each target key and row occurs in the source table, and
the parent frame makes its transported comparison equal. -/
theorem Table.RowReferencesHold.frame {before after : Database} {oldMapping newMapping : ForeignKeyMapping}
    {move : Nat → Nat} {oldPosition position : Nat} {oldTable table : Table}
    (holds : oldTable.RowReferencesHold oldMapping before oldPosition)
    (frame : Table.RowReferenceFrame before after oldMapping newMapping move oldPosition position oldTable table) :
    table.RowReferencesHold newMapping after position := by
  intro key declared row member
  have comparison := ForeignKeyLink.satisfied_transport before after move
    (oldMapping.link oldPosition key) position row (frame.parents key declared)
  have same : newMapping.link position key =
      { child := position, key, parent := (oldMapping.parent oldPosition key).transport move } := by
    simp [ForeignKeyMapping.link, frame.mapping key declared]
  simp only [ForeignKeyMapping.link] at comparison
  rw [same, comparison]
  exact holds key (frame.declarations key declared) row (frame.rows row member)

/-- If every target table is framed by a source table and the source database has the row fact,
then the target database has it under the new mapping. Positions may change through the
explicit transport. Proof sketch: apply the table frame at each target table. -/
theorem Database.RowReferencesHold.frame {before after : Database} {oldMapping newMapping : ForeignKeyMapping}
    {move : Nat → Nat} (holds : before.RowReferencesHold oldMapping)
    (frames : ∀ position table, after.table position = some table →
      ∃ oldPosition oldTable, before.table oldPosition = some oldTable ∧
        Table.RowReferenceFrame before after oldMapping newMapping move oldPosition position oldTable table) :
    after.RowReferencesHold newMapping := by
  intro position table present
  obtain ⟨oldPosition, oldTable, found, frame⟩ := frames position table present
  exact (holds oldPosition oldTable found).frame frame

end Belay.Sqlite.Model
