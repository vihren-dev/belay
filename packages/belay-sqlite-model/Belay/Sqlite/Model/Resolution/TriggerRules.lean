import Belay.Sqlite.Model.Resolution.TriggerClosure
import Belay.Sqlite.Model.Resolution.ForeignKeyResolution

set_option doc.verso true

/-! The trigger programs of a resolved write (ADR 0018, D5): the closure of its request
({name}`Belay.Sqlite.Model.triggerClosure`), the newest trigger first, and the restriction of a
{lit}`BEFORE UPDATE` or {lit}`BEFORE DELETE` trigger that writes its own table, whose result
SQLite documents as undefined. -/

namespace Belay.Sqlite.Model

/-- The request of a resolved write ({name}`FireRequest`): its table and event, and for the
DELETE of DROP TABLE with foreign keys on, one that fires no trigger of the table; none for a
statement that writes no row. -/
def Resolved.Statement.fireRequest (keys : Bool) : Resolved.Statement → Option FireRequest
  | .insert table _ _ _ _ => some { table, event := .insert }
  | .upsert table _ _ _ algorithm _ _ => some { table, event := .insert, algorithm }
  | .update table assignments _ _ _ _ => some { table, event := .update (some (assignments.map (·.1))) }
  | .delete table _ _ _ _ => some { table, event := .delete }
  | .drop (table :: _) _ => if keys then some { table, event := .delete, fire := false } else none
  | .drop [] _ | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .begin | .commit | .rollback
  | .prepareError _ | .query .. | .setting _ => none

/-- Whether the catalog has a trigger on the table at the position. -/
def Catalog.triggersOn (catalog : Catalog) (table : Nat) : Bool :=
  catalog.any fun object => match object.entry with
    | .trigger trigger => (catalog.findTable trigger.table).any (·.1 == table)
    | .table _ | .index _ => false

/-- The tables that the requests write, with the writes that they cause through the programs
that they fire and, with foreign keys on, their {name}`FireRequest.keyRequests`, each request
once; none when requests are left past the fuel. -/
def writtenTables (catalog : Catalog) (keys : Bool) (programs : List Resolved.Program) :
    Nat → List FireRequest → List FireRequest → Option (List Nat)
  | 0, _, work => if work.isEmpty then some [] else none
  | _ + 1, _, [] => some []
  | fuel + 1, seen, request :: rest =>
    let fired := programs.filter fun program =>
      request.fire && program.table == request.table && program.event.fires request.event
    let next := (if keys then request.keyRequests catalog catalog.foreignKeyLinks else []) ++
      fired.flatMap (·.body.filterMap (·.request request.algorithm))
    let fresh := next.eraseDups.filter fun item => !seen.contains item && !rest.contains item
    (request.table :: ·) <$> writtenTables catalog keys programs fuel (seen ++ fresh) (rest ++ fresh)

/-- The fuel of a closure over the catalog: enough for the requests of the catalog's triggers and
foreign keys in the cases that the model describes. -/
def closureFuel (catalog : Catalog) : Nat := 8 * (catalog.length + catalog.foreignKeyLinks.length + 1)

/-- Whether the program is a {lit}`BEFORE UPDATE` or {lit}`BEFORE DELETE` program that writes
its own table, directly or through what its writes cause ({name}`writtenTables`), or past the
fuel. -/
def Resolved.Program.writesOwnTable (catalog : Catalog) (keys : Bool) (programs : List Resolved.Program)
    (program : Resolved.Program) : Bool :=
  match program.time, program.event with
  | .before, .update _ | .before, .delete =>
    let start := program.body.filterMap (·.request none)
    ((writtenTables catalog keys programs (closureFuel catalog) start start).map (·.contains program.table)).getD true
  | .before, .insert | .after, .insert | .after, .update _ | .after, .delete => false

/-- The programs with one more inserted before the first program of an older trigger, so that
the newest trigger comes first. -/
def insertNewest (program : Resolved.Program) : List Resolved.Program → List Resolved.Program
  | [] => [program]
  | first :: rest => if program.trigger ≥ first.trigger then program :: first :: rest else first :: insertNewest program rest

/-- The trigger programs of a resolved write at the index over the catalog, with foreign keys
checked when {lit}`keys` is set: the closure of its request, the newest trigger first; a prepare
error of a program; or a restriction, such as {name}`RestrictionKind.triggerWritesOwnTable`, or
{name}`RestrictionKind.triggerForm` for {lit}`ON CONFLICT DO UPDATE` on a table with a trigger,
whose UPDATE triggers the closure does not follow. A statement that writes no row has none. -/
def triggerPrograms (context : ResolveContext) (catalog : Catalog) (index : Nat) (keys : Bool)
    (statement : Resolved.Statement) : Except Restriction (Except PrepareError (List Resolved.Program)) := do
  let some request := statement.fireRequest keys | pure (.ok [])
  if statement.updatesOnConflict && catalog.triggersOn request.table then throw (triggerRestriction index .triggerForm)
  match ← triggerClosure context catalog index keys (closureFuel catalog) [request] [request] [] with
  | .error error => pure (.error error)
  | .ok programs =>
    if programs.any (·.writesOwnTable catalog keys programs) then throw (triggerRestriction index .triggerWritesOwnTable)
    pure (.ok (programs.foldr insertNewest []))

end Belay.Sqlite.Model
