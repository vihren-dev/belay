import Belay.Sqlite.Model.Programs.Scripts.SchemaPath
import Belay.Sqlite.Model.Programs.Scripts.TableKeeps

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Follow a table through the first statements of a resolved script. Zero gives its
initial position. After the end of the script the result stays at the final position.
{lean}`(none : Option Nat)` means a statement could change the table. -/
def ResolveState.tablePosition (initial : ResolveState) (resolved : List Resolved.Statement)
    (count position : Nat) : Option Nat :=
  match count, resolved with
  | 0, _ | _, [] => some position
  | n + 1, first :: rest => (first.keeps initial.catalog position).bind fun moved =>
    (initial.after first).tablePosition rest n moved

/-- At each position containing a statement, following a table through one more step
applies that statement's check to the preceding position and catalog. Proof sketch:
induct on the prefix, passing the position from one statement to the next. -/
theorem ResolveState.tablePosition_succ {initial : ResolveState} {resolved : List Resolved.Statement}
    {n : Nat} {statement : Resolved.Statement} (atStmt : resolved[n]? = some statement) (position : Nat) :
    initial.tablePosition resolved (n + 1) position = (initial.tablePosition resolved n position).bind
      (statement.keeps (initial.atPrefix resolved n).catalog) := by
  induction n generalizing initial resolved position with
  | zero =>
    cases resolved with
    | nil => simp at atStmt
    | cons first rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atStmt
      subst statement
      simp [tablePosition, atPrefix]
  | succ n ih =>
    cases resolved with
    | nil => simp at atStmt
    | cons first rest =>
      have tail : rest[n]? = some statement := by simpa using atStmt
      simp only [tablePosition, Option.bind_assoc]
      cases moved : first.keeps initial.catalog position with
      | none => rfl
      | some p => exact ih tail p

/-- If following the original table through a prefix gives a position, the database holds
that table at the reported position. A prefix whose check fails imposes no condition. -/
def ResolveState.TableAtPrefix (initial : ResolveState) (resolved : List Resolved.Statement)
    (n start : Nat) (table : Table) (database : Database) : Prop :=
  ∀ p, initial.tablePosition resolved n start = some p → database.table p = some table

/-- A table present in the database satisfies the table check at the empty prefix. -/
theorem ResolveState.tableAtPrefix_zero {initial : ResolveState} {resolved : List Resolved.Statement}
    {start : Nat} {database : Database} {table : Table} (present : database.table start = some table) :
    initial.TableAtPrefix resolved 0 start table database := by
  intro p check
  simp only [tablePosition, Option.some.injEq] at check
  exact check ▸ present

/-- For each statement of a resolved script and each successful execution of its step,
if the connection has the schema of the prefix and holds a tracked table wherever the
prefix check places it, the next database holds that table wherever the next prefix check
places it. Proof sketch: read the statement's resolution from the script certificate.
The prefix recurrence gives the input position for the single-statement frame. -/
theorem runScriptStep_tableAtPrefix {context : ResolveContext} {clock : Option Clock}
    {initial final : ResolveState} {resolved : List Resolved.Statement} {script : List Syntax.Statement}
    {offset index n start : Nat} {statement : Syntax.Statement} {parameters : List Value}
    {c next : Connection} {output : Output} {others : List StatementExecution} {table : Table}
    (checked : resolveFrom context offset initial script = .ok (resolved, final))
    (atStmt : script[n]? = some statement) (same : c.resolveState = initial.atPrefix resolved n)
    (tracked : initial.TableAtPrefix resolved n start table c.state.database)
    (step : runScriptStep context clock index c statement parameters = .continued output next others)
    {found : StatementExecution} (member : found ∈ (RunStep.continued output next others).executions)
    (ok : found.output.isError = false) : initial.TableAtPrefix resolved (n + 1) start table
      found.next.state.database := by
  obtain ⟨r, atR, resolution⟩ := resolveFrom_atPrefix checked atStmt
  rw [← same] at resolution
  intro p check
  rw [ResolveState.tablePosition_succ atR] at check
  obtain ⟨old, previous, moved⟩ := Option.bind_eq_some_iff.mp check
  rw [← same] at moved
  exact runScriptStep_keepsTable resolution moved (tracked old previous) step member ok

end Belay.Sqlite.Model
