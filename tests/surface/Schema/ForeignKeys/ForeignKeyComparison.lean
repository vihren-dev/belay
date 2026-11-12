import Belay

/-! Kernel checks of the lookup/scan premise and its structural sufficient conditions. -/

open Belay.Sqlite.Model
set_option doc.verso true
set_option maxRecDepth 4096

/-- A BLOB-affinity column, whose values are not coerced. -/
def blobColumn : CatalogColumn := { name := .ofString "k", declaredType := none }
/-- A TEXT column with NOCASE collation, to keep the collation parameter visible. -/
def textColumn : CatalogColumn := { name := .ofString "k", declaredType := some "TEXT", collation := .nocase }
/-- An INTEGER-affinity child column used in the necessary-premise counterexample. -/
def integerColumn : CatalogColumn := { name := .ofString "k", declaredType := some "INTEGER" }
/-- A single-column child link to a selected single-column parent comparison. -/
def link : ForeignKeyLink :=
  { child := 1
    key := {
      table := .ofString "p"
      columns := [0]
      referenced := [.ofString "k"]
      onDelete := .noAction
      onUpdate := .noAction }
    parent := .located 0 (.columns [(0, 0)]) }

/-- Any stored rows of two BLOB columns give the same lookup and scan result.
The proof applies the structural theorem with the concrete column definitions. -/
theorem blobConsistent : link.LookupScanConsistent { columns := [blobColumn] }
    { columns := [blobColumn] } (.columns [(0, 0)]) :=
  ForeignKeyLink.lookupScanConsistent_blob link _ _ 0 0 blobColumn blobColumn rfl rfl rfl rfl

/-- Any stored rows of these TEXT columns give the same lookup and NOCASE scan result.
The proof applies the structural theorem, which uses storedness rather than an input-row list. -/
theorem textConsistent : link.LookupScanConsistent { columns := [textColumn] }
    { columns := [textColumn] } (.columns [(0, 0)]) :=
  ForeignKeyLink.lookupScanConsistent_text link _ _ 0 0 textColumn textColumn rfl rfl rfl rfl

/-- A TEXT parent and INTEGER child need not satisfy the premise: parent '01' and child 1
match in the numeric scan, but the parent's TEXT lookup does not match them.
The proof specializes the universal premise to that stored row pair. -/
theorem mixedInconsistent : ¬ link.LookupScanConsistent { columns := [integerColumn] }
    { columns := [textColumn] } (.columns [(0, 0)]) := by
  intro consistent
  have different := consistent { rowid := 1, values := [.text [48, 49]] }
    { rowid := 1, values := [.integer 1] } (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have impossible : childMatches { columns := [integerColumn] } { columns := [textColumn] } link
      (.columns [(0, 0)]) { rowid := 1, values := [.text [48, 49]] } { rowid := 1, values := [.integer 1] } ≠
      parentFound { columns := [textColumn] } (.columns [(0, 0)]) link [.integer 1]
        [{ rowid := 1, values := [.text [48, 49]] }] none := by decide +kernel
  exact impossible different

#print axioms blobConsistent
#print axioms textConsistent
#print axioms mixedInconsistent
#print axioms ForeignKeyLink.lookupScanConsistent_blob
#print axioms ForeignKeyLink.lookupScanConsistent_text
#print axioms Row.Stored.getD
