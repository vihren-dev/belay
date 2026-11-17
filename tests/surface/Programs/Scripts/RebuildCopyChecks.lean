import RebuildCopyFacts
import Belay.Sqlite.Model.Schema.Writes.CopyCompatibility
import Belay.Sqlite.Model.Schema.Writes.CopyProductions

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

/-- A partial index reads ids 3 and 1 by their indexed values. The complement supplies
id 2. The default table scan reads all three by rowid. -/
private def indexedSource : Belay.Sqlite.Database := db! r"
  CREATE TABLE source(id INTEGER PRIMARY KEY, v INTEGER);
  CREATE INDEX by_v ON source(v) WHERE v >= 20;
  INSERT INTO source VALUES(1, 30), (2, 10), (3, 20);"

/-- Copying this source can return either access order, with the same cells and no failure. -/
example : (Resolved.Query.copyOf 0 2 ["id", "v"]).productions (.plain 0) indexedSource.raw false =
    some [⟨[[1, 30], [2, 10], [3, 20]], none⟩, ⟨[[3, 20], [1, 30], [2, 10]], none⟩] := by decide +kernel
