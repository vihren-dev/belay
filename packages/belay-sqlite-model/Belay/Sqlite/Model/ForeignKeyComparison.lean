import Belay.Sqlite.Model.ForeignKeyMatch
import Belay.Sqlite.Model.DatabaseFacts

set_option doc.verso true

/-! Conditions under which a parent's child scan agrees with a child's parent lookup.
These conditions quantify over future stored rows as well as the rows of an input database.
They expose the comparison premise that enforcement alone does not provide. -/

namespace Belay.Sqlite.Model

/-- For the supplied link, table definitions and comparison key, every pair of stored rows
with no selected NULL child value gives the same Boolean result from {name}`childMatches`
and a lookup in the singleton parent row with {name}`parentFound`. Rows with a selected NULL
value impose nothing. The comparison key must separately be the key selected by the mapping.
This is a comparison property, not a claim that the parent row exists in a database. -/
def ForeignKeyLink.LookupScanConsistent (link : ForeignKeyLink) (child parent : CatalogTable)
    (key : ParentKey) : Prop :=
  ∀ parentRow childRow, parentRow.Stored parent.columns → childRow.Stored child.columns →
    link.hasNull childRow.values = false →
    childMatches child parent link key parentRow childRow =
      parentFound parent key link childRow.values [parentRow] none

/-- For a stored row and an existing column, reading the cell with NULL as the fallback
gives a value unchanged by that column's affinity. A missing cell reads NULL.
The proof splits on whether the cell exists and applies storedness when it does. -/
theorem Row.Stored.getD {row : Row} {columns : List CatalogColumn} (stored : row.Stored columns)
    {position : Nat} {column : CatalogColumn} (found : columns[position]? = some column) :
    Value.store column.affinity (row.values.getD position .null) = row.values.getD position .null := by
  rw [List.getD_eq_getElem?_getD]
  cases cell : row.values[position]? with
  | none => cases column.affinity <;> rfl
  | some value => exact stored position column value found cell

/-- For a single selected column pair whose parent has BLOB affinity and whose child has
nonnumeric affinity, the scan and lookup agree for every stored row pair with no selected
NULL. The parent column's collation is unrestricted. The proof reduces both operations
to the same comparison without an affinity conversion. -/
theorem ForeignKeyLink.lookupScanConsistent_blob (link : ForeignKeyLink) (child parent : CatalogTable)
    (childPosition parentPosition : Nat) (childColumn parentColumn : CatalogColumn)
    (childFound : child.columns[childPosition]? = some childColumn)
    (parentFoundColumn : parent.columns[parentPosition]? = some parentColumn)
    (parentAffinity : parentColumn.affinity = .blob)
    (childAffinity : numericAffinity childColumn.affinity = false) :
    link.LookupScanConsistent child parent (.columns [(childPosition, parentPosition)]) := by
  intro parentRow childRow _ _ _
  have comparison : comparisonAffinity (some .blob) (some childColumn.affinity) =
      some .blob := by simp [comparisonAffinity, childAffinity, show numericAffinity .blob = false from rfl]
  simp [childMatches, parentCell, childFound, parentFoundColumn, comparison,
    Resolved.comparisonOperands, parentFound, childValues, childPositions, parentAffinity, numericAffinity,
    indexHolds, indexAffinity, Value.store]

/-- For a single selected column pair whose parent and child both have TEXT affinity,
the scan and lookup agree for every stored row pair with no selected NULL, under the
parent column's collation. The proof uses the child's storedness to remove the lookup's
TEXT conversion; neither operation then changes either cell. -/
theorem ForeignKeyLink.lookupScanConsistent_text (link : ForeignKeyLink) (child parent : CatalogTable)
    (childPosition parentPosition : Nat) (childColumn parentColumn : CatalogColumn)
    (childFound : child.columns[childPosition]? = some childColumn)
    (parentFoundColumn : parent.columns[parentPosition]? = some parentColumn)
    (parentAffinity : parentColumn.affinity = .text) (childAffinity : childColumn.affinity = .text) :
    link.LookupScanConsistent child parent (.columns [(childPosition, parentPosition)]) := by
  intro parentRow childRow _ childStored _
  have stored := childStored.getD childFound
  rw [childAffinity] at stored
  simp only [List.getD_eq_getElem?_getD] at stored
  simp [childMatches, parentCell, childFound, parentFoundColumn, parentAffinity, childAffinity,
    comparisonAffinity, numericAffinity, Resolved.comparisonOperands, parentFound, childValues, childPositions,
    indexHolds, indexAffinity, stored]

end Belay.Sqlite.Model
