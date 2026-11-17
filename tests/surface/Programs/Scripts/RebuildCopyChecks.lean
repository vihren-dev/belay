import RebuildCopyFacts
import Belay.Sqlite.Model.Schema.Writes.CopyCompatibility

/-! Exercise CatalogTable.copyCompatible on the README shapes and on changes to one
column obligation. A target may drop a NOT NULL constraint. Adding a requirement,
losing a column, or changing a storage affinity can reject or change source cells. -/

open Belay.Sqlite Belay.Sqlite.Model RebuildGuide

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-- Check the two definitions against the target's unique keys from the rebuild. -/
private def compatible (source target : CatalogTable) : Bool :=
  source.copyCompatible target ((schemaAt 3).catalog.uniqueKeys 2 target)

example : compatible sourceShape strictShape = true := by decide +kernel
example : compatible sourceShape
    { strictShape with columns := strictShape.columns.modify 2 fun c => { c with notNull := false } } = true := by
  decide +kernel
example : compatible sourceShape
    { strictShape with columns := strictShape.columns.modify 1 fun c => { c with notNull := true } } = false := by
  decide +kernel
example : compatible sourceShape { strictShape with columns := strictShape.columns.dropLast } = false := by
  decide +kernel
example : compatible sourceShape
    { strictShape with columns := strictShape.columns.modify 2 fun c => { c with declaredType := some "BLOB", strictType := some .blob } } = false := by
  decide +kernel
