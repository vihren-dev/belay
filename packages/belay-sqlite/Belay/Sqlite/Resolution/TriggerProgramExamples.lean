import Belay.Sqlite.Resolution.Examples

set_option doc.verso true

/-! Examples of the trigger programs that resolution gives a write (ADR 0018, D5), checked when
the package builds: the cells of {lit}`NEW` and {lit}`OLD`, a prepare error of a body at the
write, the forms of {lit}`RAISE`, the order of two triggers, {lit}`UPDATE OF`, the closure over
the triggers that a body fires, and the restrictions of the slice. The authored corpus of the
slice checks the same rules against native SQLite. -/

namespace Belay.Sqlite.Resolution.TriggerProgramExamples

open Belay.Sqlite Syntax Resolution.Examples

/-- A column without a type and without constraints. -/
def plain (text : String) : ColumnDefinition := { name := Identifier.ofString text, declaredType := none, constraints := [] }

/-- {lit}`CREATE TABLE t(a, b)` and {lit}`CREATE TABLE log(x)`. -/
def tables : List Syntax.Statement :=
  [.createTable (name! "t") [plain "a", plain "b"] [], .createTable (name! "log") [plain "x"] []]

/-- {lit}`CREATE TRIGGER name time event ON t BEGIN body END`. -/
def trigger (name : String) (time : TriggerTime) (event : TriggerEvent) (body : List BodyStatement)
    (table : String := "t") : Syntax.Statement :=
  .createTrigger (Identifier.ofString name) false time event (Identifier.ofString table) none body

/-- {lit}`INSERT INTO log VALUES (value)` in a body. -/
def logged (value : Expr) : BodyStatement := .insert (name! "log") none [[value]] []

/-- {lit}`source.column`. -/
def column (source name : String) : Expr := .qualified (Identifier.ofString source) (Identifier.ofString name)

/-- {lit}`INSERT INTO t VALUES (1, 2)`. -/
def insertT : Syntax.Statement := .insert (name! "t") none [[.numeric "1", .numeric "2"]] []

/-- {lit}`SELECT result` in a body. -/
def selected (result : Expr) (filter : Option Expr := none) : BodyStatement :=
  .select [.expression result none ""] none [] filter [] [] none none

/-- The last resolved statement of the script after the two tables. -/
def last (script : List Syntax.Statement) : Option Resolved.Statement := (statements (migration [] (tables ++ script))).getLast?

/-- The programs of the last statement of the script after the two tables. -/
def programs (script : List Syntax.Statement) : List Resolved.Program :=
  match last script with
  | some (.insert _ _ _ _ (some rules)) | some (.upsert _ _ _ _ _ _ (some rules)) | some (.update _ _ _ _ _ (some rules))
  | some (.delete _ _ _ _ (some rules)) | some (.drop _ (some rules)) => rules.programs
  | some _ | none => []

/-- Whether the script after the two tables is a restriction of the kind. -/
def restrictedAs (kind : RestrictionKind) (script : List Syntax.Statement) : Bool :=
  match migration [] (tables ++ script) with
  | .restricted restriction => restriction.kind == kind
  | .resolved .. => false

-- NEW.a is the first cell of an INSERT of the body; the trigger is the object at position 2.
#guard (programs [trigger "r" .after .insert [logged (column "new" "a")], insertT]).map (fun program =>
  (program.trigger, program.table, program.width, program.body)) == [(2, 0, 2, [.insert 1 [[.expression (.column 0)]] [] none []])]
-- OLD of an UPDATE trigger follows the two NEW cells; an UPDATE of the body reads it after its own cell.
#guard (programs [trigger "r" .after (.update []) [.update (name! "log") [(name! "x", column "old" "b")] none],
    .update (name! "t") [(name! "a", .numeric "5")] none]).map (·.body) ==
  [[.update 1 [(0, .column 4)] none []]]
-- A name that the body cannot resolve is a prepare error of the write: a missing table, OLD of
-- an INSERT trigger, and an unqualified column of the trigger's table.
#guard last [trigger "r" .after .insert [.delete (name! "nosuch") none], insertT] ==
  some (.prepareError (.noSuchTable (name! "nosuch")))
#guard (last [trigger "r" .after .insert [logged (column "old" "a")], insertT]).any (· matches .prepareError _)
#guard (last [trigger "r" .after .insert [logged (.identifier (name! "a") .none)], insertT]).any (· matches .prepareError _)
-- A body that SQLite would never prepare stays out: a DELETE does not prepare the INSERT trigger.
#guard last [trigger "r" .after .insert [.delete (name! "nosuch") none], .delete (name! "t") none] ==
  some (.delete 0 none [] [])

-- RAISE alone and as a result of CASE; RAISE in WHERE is a restriction.
#guard (programs [trigger "r" .before .insert [selected (.raise .ignore none)], insertT]).map (·.body) ==
  [[.raise none [] (some .ignore)]]
#guard (programs [trigger "r" .before .insert [selected (.caseOf [.compare .eq (column "new" "a") (.numeric "1"),
    .raise .abort (some (.string [109]))] false)], insertT]).map (·.body) ==
  [[.raise none [(.compare .eq (some .blob) (.column 0) (.literal (.integer 1)), some .abort)] none]]
#guard restrictedAs .raiseForm [trigger "r" .before .insert [selected (.numeric "1") (some (.raise .ignore none))], insertT]

-- Of two triggers of one event, the newest comes first; UPDATE OF b fires only for SET b.
#guard (programs [trigger "r" .after .insert [], trigger "s" .after .insert [], insertT]).map (·.trigger) == [3, 2]
#guard programs [trigger "r" .after (.update [name! "b"]) [], .update (name! "t") [(name! "a", .numeric "5")] none] == []
#guard (programs [trigger "r" .after (.update [name! "b"]) [], .update (name! "t") [(name! "b", .numeric "5")] none]).length == 1

-- The closure: a body's INSERT into log fires the trigger of log; a trigger that writes its own
-- table has one program.
#guard (programs [trigger "r" .after .insert [logged (.numeric "1")], trigger "s" .after .insert [] "log", insertT]).map
  (·.trigger) == [3, 2]
#guard (programs [trigger "r" .after .insert [.insert (name! "t") none [[.numeric "1", .numeric "2"]] []], insertT]).length == 1

-- A BEFORE DELETE trigger that deletes from its own table is a restriction; an AFTER one is not.
#guard restrictedAs .triggerWritesOwnTable [trigger "r" .before .delete [.delete (name! "t") none], .delete (name! "t") none]
#guard !restricted (migration [] (tables ++ [trigger "r" .after .delete [.delete (name! "t") none], .delete (name! "t") none]))

-- ON CONFLICT DO UPDATE in a body is a restriction of a trigger form.
#guard restrictedAs .triggerForm [trigger "r" .after .insert [.insert (name! "log") none [[.numeric "1"]]
    [{ target := none, action := .update [(name! "x", .numeric "2")] none }]], insertT]

-- Two triggers of one table, time and event in the starting schema are a restriction.
#guard match resolveSchemaAndScript defaults (tables ++ [trigger "r" .after .insert [], trigger "s" .after .insert []]) [insertT] with
  | .error issue => issue == .schemaRestricted { statement := 3, path := [], kind := .schemaTriggerOrder }
  | .ok _ => false

end Belay.Sqlite.Resolution.TriggerProgramExamples
