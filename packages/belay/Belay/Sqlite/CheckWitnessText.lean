import Belay.Sqlite.CheckData
import Belay.Sqlite.CounterexampleWitness
import Belay.Sqlite.ReplayValues

set_option doc.verso true

/-! The database and the environment of a counterexample as a user reads them: each table with
its rows, as {lit}`#sql` shows a result, and the clock and counters as values. The checker
computes this text from the certified witness; the text itself proves nothing. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term Belay.Sqlite.Model

/-- A value as the SQL literal that gives it, so that the cells {lit}`'a'`, {lit}`'A'`,
{lit}`1`, {lit}`'1'`, {lit}`NULL` and {lit}`X'00'` differ. It is the replay's literal
({name}`Replay.valueLiteral`); a value with no SQLite literal shows as
{name}`Belay.Sqlite.Model.Value.display` writes it. -/
def cellLiteral (value : Value) : String :=
  (Replay.valueLiteral value).getD (toString value.display)

/-- The tables of the database: for each table of the catalog, its name and then its column
names and rows as a table ({name}`textTable`), each line indented by two spaces, with
{lit}`(no rows)` for an empty table. Views, indexes and triggers have no rows and are left out,
so a database with no table gives the empty text. -/
def databaseTables (database : Database.Raw) : String :=
  let tables := database.catalog.zipIdx.filterMap fun (object, position) => match object.entry with
    | .table table =>
      let rows := database.rows.getD position []
      let body := if rows.isEmpty then textTable (table.columns.map (·.name.text)) [] ++ "\n(no rows)"
        else textTable (table.columns.map (·.name.text)) (rows.map (·.values.map cellLiteral))
      some ("\n".intercalate ((object.name.text ++ ":") :: (body.splitOn "\n").map ("  " ++ ·)))
    | .view _ | .index _ | .trigger _ => none
  "\n".intercalate tables

/-- The values of an environment that a counterexample shows: the clock of the first statement
in Julian-day milliseconds, and the counters {lit}`changes()`, {lit}`total_changes()` and
{lit}`last_insert_rowid()`. Each is none when the environment does not know it. -/
def environmentValues (environment : Env) : Option Int × Option Nat × Option Nat × Option Int :=
  (environment.clock.map (· 0), environment.counters.changes, environment.counters.totalChanges,
    environment.counters.lastInsertRowid)

/-- The text of {name}`environmentValues`: the clock as {lit}`YYYY-MM-DD HH:MM:SS` UTC, and each
counter as its value or {lit}`unknown`. For example, {lit}`clock 2025-01-01 00:00:00 at the
first statement; changes() 0, total_changes() 0, last_insert_rowid() 0`. -/
def environmentText : Option Int × Option Nat × Option Nat × Option Int → String
  | (clock, changes, totalChanges, lastInsertRowid) =>
    let time := match clock with
      | none => "no clock"
      | some milliseconds =>
        match strftimeValue milliseconds [.text "%Y-%m-%d %H:%M:%S".toUTF8.toList, .text "now".toUTF8.toList] with
        | .text bytes => s!"clock {String.fromUTF8! ⟨bytes.toArray⟩} at the first statement"
        | .null | .integer _ | .real _ | .blob _ =>
          s!"clock {milliseconds} Julian-day milliseconds at the first statement"
    let counter := fun (name : String) (value : Option String) => s!"{name} {value.getD "unknown"}"
    s!"{time}; {counter "changes()" (changes.map toString)}, " ++
      s!"{counter "total_changes()" (totalChanges.map toString)}, " ++
      counter "last_insert_rowid()" (lastInsertRowid.map toString)

/-- The text of the database and the environment of a counterexample. -/
structure WitnessText where
  /-- The constant that the witness database names, for example {lit}`sample`, or none for a
  database that the checker generated and for {name}`Database.empty`. -/
  name : Option Name := none
  /-- The tables of the database ({name}`databaseTables`). -/
  tables : String
  /-- The environment ({name}`environmentText`), or none for the checker's default candidate
  {name}`candidateEnvironment`, which a user does not need to read. -/
  environment : Option String := none

/-- Evaluate the database and environment of a witness, with the same certified evaluation as
replay ({name}`databaseValue`, {name}`dataValue`), and give their text. -/
def witnessText (witness : Witness) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM WitnessText := do
  let database ← databaseValue witness.database excluded excludedLocals
  let tables := databaseTables database.raw
  let name := match witness.database.consumeMData with
    | .const name _ => if name == ``Database.empty then none else some name
    | _ => none
  if witness.environment.consumeMData == Lean.mkConst ``candidateEnvironment then return { name, tables }
  let values ← dataValue (Option Int × Option Nat × Option Nat × Option Int)
    (mkApp (Lean.mkConst ``environmentValues) witness.environment) excluded excludedLocals
  return { name, tables, environment := some (environmentText values) }

end Belay.Sqlite.Check
