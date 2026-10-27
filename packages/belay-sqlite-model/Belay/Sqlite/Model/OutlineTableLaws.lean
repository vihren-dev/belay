import Belay.Sqlite.Model.DatabaseConstraints
import Belay.Sqlite.Model.Resolution.CatalogOutline

set_option doc.verso true

/-! The facts about the rows of one table that a rename keeps. A rename writes names only
({lit}`CatalogOutline`), and these facts read the columns of the table by position: their NOT NULL
flag, strict type, affinity and rowid alias, the conditions of the CHECK constraints, and the
number of columns. A table with the same rows and the same shape after
{lit}`CatalogTable.blankNames` has each of these facts when the other table has it. -/

namespace Belay.Sqlite.Model

/-- For every tables with one shape after {name}`CatalogTable.blankNames`, and every column of one
at a position: the other has a column at the position with the same blanked form. Proof sketch: the
columns of the blanked tables are equal lists, and the entry of a mapped list at a position is the
mapped entry. -/
theorem CatalogTable.column_of_blankNames {first second : CatalogTable}
    (same : first.blankNames = second.blankNames) {position : Nat} {column : CatalogColumn}
    (found : first.columns[position]? = some column) :
    ∃ other, second.columns[position]? = some other ∧ other.blankNames = column.blankNames := by
  have columns := congrArg (fun table => table.columns[position]?) same
  simp only [CatalogTable.blankNames, List.getElem?_map, found, Option.map_some] at columns
  cases other : second.columns[position]? with
  | none => simp [other] at columns
  | some value =>
    simp only [other, Option.map_some, Option.some.injEq] at columns
    exact ⟨value, rfl, columns.symm⟩

/-- For every tables with one shape after {name}`CatalogTable.blankNames`: the same number of
columns. Proof sketch: the lengths of the blanked column lists. -/
theorem CatalogTable.columns_length_of_blankNames {first second : CatalogTable}
    (same : first.blankNames = second.blankNames) : first.columns.length = second.columns.length := by
  simpa [CatalogTable.blankNames] using congrArg (fun table => table.columns.length) same

/-- For every tables with one shape after {name}`CatalogTable.blankNames`: the same rowid alias.
Proof sketch: the field is not blanked. -/
theorem CatalogTable.rowidAlias_of_blankNames {first second : CatalogTable}
    (same : first.blankNames = second.blankNames) : first.rowidAlias = second.rowidAlias :=
  congrArg (fun table => table.rowidAlias) same

/-- The blanked table has the blanked CHECK constraints of the table. Proof sketch: the lists of
the columns map and flatten. -/
theorem CatalogTable.allChecks_blankNames (table : CatalogTable) :
    table.blankNames.allChecks = table.allChecks.map CheckConstraint.blankNames := by
  simp [CatalogTable.allChecks, CatalogTable.blankNames, List.flatMap_map, List.map_flatMap, CatalogColumn.blankNames]

/-- For every tables with one shape after {name}`CatalogTable.blankNames` and every CHECK constraint
of the second: the first has one with the same condition. Proof sketch: the blanked CHECK lists are
equal ({name}`CatalogTable.allChecks_blankNames`), and blanking keeps the condition. -/
theorem CatalogTable.check_of_blankNames {first second : CatalogTable}
    (same : first.blankNames = second.blankNames) {check : CheckConstraint} (member : check ∈ second.allChecks) :
    ∃ other ∈ first.allChecks, other.condition = check.condition := by
  have checks := congrArg CatalogTable.allChecks same
  rw [CatalogTable.allChecks_blankNames, CatalogTable.allChecks_blankNames] at checks
  have blanked : check.blankNames ∈ first.allChecks.map CheckConstraint.blankNames := by
    rw [checks]
    exact List.mem_map_of_mem member
  obtain ⟨other, found, equal⟩ := List.mem_map.mp blanked
  exact ⟨other, found, by simpa [CheckConstraint.blankNames] using congrArg (fun check => check.condition) equal⟩

/-- For every tables with the same rows and one shape after {name}`CatalogTable.blankNames`: if
the first table has {name}`Table.NotNull`, the second has it. Proof sketch: a column of the second
table at a position is the blanked form of one of the first, which has the same NOT NULL flag. -/
theorem Table.NotNull.of_blankNames {first second : Table} (rows : second.rows = first.rows)
    (same : first.shape.blankNames = second.shape.blankNames) (holds : first.NotNull) : second.NotNull := by
  intro row member position column value found cell flagged
  rw [rows] at member
  obtain ⟨other, foundFirst, blanked⟩ := CatalogTable.column_of_blankNames same.symm found
  have flag := congrArg CatalogColumn.notNull blanked
  exact holds row member position other value foundFirst cell (flag.trans flagged)

/-- For every tables with the same rows and one shape after {name}`CatalogTable.blankNames`: if
the first table has {name}`Table.TypesFit`, the second has it. Proof sketch: as
{name}`Table.NotNull.of_blankNames`, with the strict type. -/
theorem Table.TypesFit.of_blankNames {first second : Table} (rows : second.rows = first.rows)
    (same : first.shape.blankNames = second.shape.blankNames) (holds : first.TypesFit) : second.TypesFit := by
  intro row member position column value found cell
  rw [rows] at member
  obtain ⟨other, foundFirst, blanked⟩ := CatalogTable.column_of_blankNames same.symm found
  have strict := congrArg CatalogColumn.strictType blanked
  have fits := holds row member position other value foundFirst cell
  simpa [CatalogColumn.blankNames] using strict ▸ fits

/-- For every tables with the same rows and one shape after {name}`CatalogTable.blankNames`: if
the first table has {name}`Table.ChecksHold`, the second has it. Proof sketch: a CHECK constraint
of the second table has the condition of one of the first
({name}`CatalogTable.check_of_blankNames`), and the check reads the condition only. -/
theorem Table.ChecksHold.of_blankNames {first second : Table} (rows : second.rows = first.rows)
    (same : first.shape.blankNames = second.shape.blankNames) (holds : first.ChecksHold) : second.ChecksHold := by
  intro row member check checkMember
  rw [rows] at member
  obtain ⟨other, otherMember, condition⟩ := CatalogTable.check_of_blankNames same checkMember
  have kept := holds row member other otherMember
  simpa [LiteralData.checkHolds, condition] using kept

end Belay.Sqlite.Model
