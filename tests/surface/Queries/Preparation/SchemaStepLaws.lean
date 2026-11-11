import Belay

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_schema_script_test.py`: the helpers of the examples of the step, frame and
success laws of the schema and transaction statements (ADR 0017, S6, task {lit}`20261027-schema-script-laws`) on a
concrete database. The parent {lit}`p` is at position 0 of the catalog and the child {lit}`c` at position 1; the child
refers to the parent with {lit}`ON DELETE CASCADE`. The helpers take the step of a statement from a connection, find a
table by name with its rows, and check by the kernel how a statement resolves. The later modules
({lit}`SchemaDropExamples`, {lit}`SchemaCreateExamples`) use the laws with them. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace SchemaStepLaws

/-- The parent and the child of the examples. -/
def family : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(id INTEGER PRIMARY KEY, name TEXT);
  INSERT INTO p VALUES(1,'x'),(2,'y');
  CREATE TABLE c(id INTEGER PRIMARY KEY, pid INTEGER REFERENCES p(id) ON DELETE CASCADE, note TEXT);
  INSERT INTO c VALUES(10,1,'a'),(11,2,'b'),(12,2,'c');"

/-- A complete environment with a constant clock and no known counters. -/
def environment : Env := { clock := some (fun _ => 0) }

/-- The connection of the database with foreign keys off, as a new connection has them. -/
def start : Connection := family.raw.connection environment.counters

/-- The connection of the database with foreign-key enforcement on. -/
def enforcing : Connection := { start with foreignKeys := true }

/-- The first statement of a one-statement script. -/
def statementOf (script : Script) (nonempty : script.statements ≠ [] := by decide +kernel) : Syntax.Statement :=
  (script.statements.head nonempty).1

/-- The step of a statement at index 0 of a connection, with the clock of the environment. -/
def stepOf (connection : Connection) (statement : Syntax.Statement) : RunStep :=
  runScriptStep runContext environment.clock 0 connection statement []

/-- The rows of the table that a name finds in a database, with its position. -/
def foundRows (database : Model.Database) (name : Identifier) : Option (Nat × List (Int × List Value)) :=
  (database.tableNamed name).map fun (position, table) => (position, table.rows.map fun row => (row.rowid, row.values))

/-- Whether a statement resolves, on a connection, to the expected resolved statement. -/
def resolvesTo (connection : Connection) (statement : Syntax.Statement) (expected : Resolved.Statement) : Bool :=
  match resolveStatement runContext connection.resolveState statement with
  | .ok (resolved, _) => decide (resolved = expected)
  | .error _ => false

/-- If the check succeeds, the statement resolves to the expected statement. Proof sketch: invert the match. -/
theorem resolvesTo_sound {connection : Connection} {statement : Syntax.Statement} {expected : Resolved.Statement}
    (checked : resolvesTo connection statement expected = true) :
    ∃ after, resolveStatement runContext connection.resolveState statement = .ok (expected, after) := by
  unfold resolvesTo at checked
  split at checked
  · rename_i resolved after same
    simp at checked
    exact ⟨after, by rw [same, checked]⟩
  · cases checked

/-- If a name finds a table at a position by the check of positions, the table exists. Proof sketch: case split on
the lookup. -/
theorem tableNamed_exists {database : Model.Database} {name : Identifier} {position : Nat}
    (found : (database.tableNamed name).map (·.1) = some position) :
    ∃ table, database.tableNamed name = some (position, table) := by
  cases lookup : database.tableNamed name with
  | none => simp [lookup] at found
  | some pair =>
    obtain ⟨place, table⟩ := pair
    simp only [lookup, Option.map_some, Option.some.injEq] at found
    subst found
    exact ⟨table, rfl⟩

/-- The rows of {lit}`p` and {lit}`c` before every step. -/
theorem start_rows : foundRows start.state.database (name! "p") = some (0, [(1, [.integer 1, .text [120]]), (2, [.integer 2, .text [121]])]) ∧
    foundRows start.state.database (name! "c") = some (1, [(10, [.integer 10, .integer 1, .text [97]]),
      (11, [.integer 11, .integer 2, .text [98]]), (12, [.integer 12, .integer 2, .text [99]])]) := by
  decide +kernel

/-- The connection after the step of a statement, if the step continues. -/
def afterStep (connection : Connection) (statement : Syntax.Statement) : Option Connection :=
  match stepOf connection statement with
  | .continued _ next _ => some next
  | .ended _ => none

/-- The output of the step of a statement, if the step continues. -/
def outputOf (connection : Connection) (statement : Syntax.Statement) : Option Output :=
  match stepOf connection statement with
  | .continued output _ _ => some output
  | .ended _ => none

/-- The step of a statement that the check proves to continue gives its facts about the connection. Proof sketch: case
split on the step. -/
theorem afterStep_of_continued {connection next : Connection} {statement : Syntax.Statement} {output : Output}
    {others : List StatementExecution} (step : stepOf connection statement = .continued output next others) :
    afterStep connection statement = some next := by
  unfold afterStep
  rw [step]

/-- Whether a statement resolves on a connection. -/
def resolves (connection : Connection) (statement : Syntax.Statement) : Bool :=
  match resolveStatement runContext connection.resolveState statement with
  | .ok _ => true
  | .error _ => false

/-- If a statement resolves, it resolves to some statement and resolution state. Proof sketch: invert the match. -/
theorem resolves_sound {connection : Connection} {statement : Syntax.Statement} (checked : resolves connection statement = true) :
    ∃ resolved after, resolveStatement runContext connection.resolveState statement = .ok (resolved, after) := by
  unfold resolves at checked
  split at checked
  · rename_i pair same
    exact ⟨pair.1, pair.2, same⟩
  · cases checked

/-- The kind of a resolved statement that the examples tell apart: a CREATE TABLE at a position with a name, a drop
with rules (foreign keys on, or trigger programs) of some positions, and every other statement. -/
inductive Shape where
  /-- A CREATE TABLE of the name at the position. -/
  | createTable (position : Nat) (name : Identifier)
  /-- A drop of the positions that comes with rules. -/
  | dropWithRules (positions : List Nat)
  /-- Every other resolved statement. -/
  | other
deriving DecidableEq

/-- The kind of a resolved statement. Every constructor of {name}`Resolved.Statement` has its own case, so a new
constructor makes this definition fail to compile until it is classified. -/
def shapeOf : Resolved.Statement → Shape
  | .createTable position name _ => .createTable position name
  | .drop positions (some _) => .dropWithRules positions
  | .drop _ none => .other
  | .createView .. => .other
  | .createIndex .. => .other
  | .createTrigger .. => .other
  | .addColumn .. => .other
  | .rewrite _ => .other
  | .dropColumn .. => .other
  | .begin => .other
  | .commit => .other
  | .rollback => .other
  | .insert .. => .other
  | .update .. => .other
  | .upsert .. => .other
  | .insertSelect .. => .other
  | .delete .. => .other
  | .prepareError _ => .other
  | .query .. => .other
  | .setting .. => .other

/-- Whether a statement resolves, on a connection, to a resolved statement of the given kind. -/
def resolvesShape (connection : Connection) (statement : Syntax.Statement) (shape : Shape) : Bool :=
  match resolveStatement runContext connection.resolveState statement with
  | .ok (resolved, _) => decide (shapeOf resolved = shape)
  | .error _ => false

/-- If a statement resolves to the kind CREATE TABLE of a name at a position, it resolves to a CREATE TABLE of that
name and position. Proof sketch: invert the match and the constructor of the resolved statement. -/
theorem resolvesShape_createTable {connection : Connection} {statement : Syntax.Statement} {position : Nat}
    {name : Identifier} (checked : resolvesShape connection statement (.createTable position name) = true) :
    ∃ table after, resolveStatement runContext connection.resolveState statement =
      .ok (.createTable position name table, after) := by
  unfold resolvesShape at checked
  split at checked
  · rename_i resolved after same
    simp only [decide_eq_true_eq] at checked
    cases resolved
    case createTable target created table =>
      simp only [shapeOf, Shape.createTable.injEq] at checked
      obtain ⟨rfl, rfl⟩ := checked
      exact ⟨table, after, same⟩
    case drop dropped rules => cases rules <;> simp only [shapeOf, reduceCtorEq] at checked
    all_goals simp only [shapeOf, reduceCtorEq] at checked
  · cases checked

/-- If a statement resolves to the kind drop with rules of some positions, it resolves to a drop of those positions
with some rules. Proof sketch: invert the match and the constructors of the resolved statement. -/
theorem resolvesShape_dropWithRules {connection : Connection} {statement : Syntax.Statement} {positions : List Nat}
    (checked : resolvesShape connection statement (.dropWithRules positions) = true) :
    ∃ rules after, resolveStatement runContext connection.resolveState statement =
      .ok (.drop positions (some rules), after) := by
  unfold resolvesShape at checked
  split at checked
  · rename_i resolved after same
    simp only [decide_eq_true_eq] at checked
    cases resolved <;> try (simp only [shapeOf, reduceCtorEq] at checked; done)
    rename_i dropped rules
    cases rules <;> simp only [shapeOf, reduceCtorEq, Shape.dropWithRules.injEq] at checked
    subst checked
    exact ⟨_, after, same⟩
  · cases checked

end SchemaStepLaws
