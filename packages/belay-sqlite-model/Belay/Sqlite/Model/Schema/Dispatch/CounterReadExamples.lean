import Belay.Sqlite.Model.Schema.Writes.CounterRowExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.CounterReadExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ScriptRunExamples

/-- The reason of the restriction of a script, or none when the script resolves. -/
def restrictionOf (script : List Syntax.Statement) : Option RestrictionKind :=
  match migration [] script with
  | .restricted restriction => some restriction.kind
  | .resolved .. => none

/-- A counter in a {lit}`CHECK` or a {lit}`DEFAULT` is a restriction. -/
example : restrictionOf [.createTable (name! "c") [column (name! "a")]
    [.check (.compare .gt (.call "changes" []) (.numeric "0")) ""]] = some .checkFunction := by decide +kernel
example : restrictionOf [.createTable (name! "c")
    [{ name := name! "a", declaredType := none, constraints := [.default (.call "changes" []) "changes()"] }] []] =
    some .unmodeledDefault := by decide +kernel

/-- {lit}`last_insert_rowid()` in an INSERT is a restriction. -/
example : restrictionOf [createT, .insert (name! "t") none [[.call "last_insert_rowid" [], .null]] []] =
    some .connectionCounterRead := by decide +kernel

/-- {lit}`total_changes()` in an INSERT without trigger programs and foreign-key actions is described,
and {lit}`last_insert_rowid()` in an UPDATE and a DELETE is described. -/
example : restrictionOf [createT, .insert (name! "t") none [[.numeric "1", .call "total_changes" []]] []] = none := by
  decide +kernel
example : restrictionOf [createT, .update (name! "t") [(name! "name", .call "last_insert_rowid" [])] none []] = none := by
  decide +kernel
example : restrictionOf [createT, .delete (name! "t") (some (.compare .eq (.identifier (name! "id") .none) (.call "last_insert_rowid" []))) []] = none := by
  decide +kernel

end Belay.Sqlite.Model.CounterReadExamples
