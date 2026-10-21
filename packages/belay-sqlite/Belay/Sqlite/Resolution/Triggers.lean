import Belay.Sqlite.Resolution.Syntax

set_option doc.verso true

/-! The triggers of the catalog (ADR 0018, D5). SQLite keeps a trigger's text and prepares its
statements when a write that runs it is prepared, against the catalog at that point, so the
catalog keeps the trigger as written; each write resolves the triggers that it may run. -/

namespace Belay.Sqlite

/-- One trigger as written: the table that it is on, as written, its time and event, its
{lit}`WHEN` condition, none without one, and the statements of its body. Its name is the name
of its catalog object. -/
structure CatalogTrigger where
  /-- The table of {lit}`ON table`, as written. -/
  table : Identifier
  /-- {lit}`BEFORE` or {lit}`AFTER`. -/
  time : Syntax.TriggerTime
  /-- {lit}`INSERT`, {lit}`UPDATE [OF columns]` or {lit}`DELETE`. -/
  event : Syntax.TriggerEvent
  /-- The {lit}`WHEN` condition; none without one. -/
  condition : Option Syntax.Expr := none
  /-- The statements of the body, in order. -/
  body : List Syntax.BodyStatement
  deriving Repr, DecidableEq

end Belay.Sqlite
