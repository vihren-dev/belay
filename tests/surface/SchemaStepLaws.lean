import Belay

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_schema_script_test.py`: the step, frame and success laws of the schema and
transaction statements (ADR 0017, S6, task {lit}`20261027-schema-script-laws`) on a concrete database. The parent
{lit}`p` is at position 0 of the catalog and the child {lit}`c` at position 1; the child refers to the parent with
{lit}`ON DELETE CASCADE`. Each example takes one step of a statement from the connection of the database, uses the law
of the statement, and checks the concrete result that the law states. The examples that need a premise show why: with
foreign keys on, the drop of the parent changes the child. -/

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

/-- Whether a statement resolves, on a connection, to a resolved statement for which the check holds. -/
def resolvesWith (connection : Connection) (statement : Syntax.Statement) (check : Resolved.Statement → Bool) : Bool :=
  match resolveStatement runContext connection.resolveState statement with
  | .ok (resolved, _) => check resolved
  | .error _ => false

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

-- DROP TABLE

/-- The statement that drops the parent. -/
def dropParent : Syntax.Statement := .dropTable (name! "p") false

/-- The script text of the drop is the statement {lean}`dropParent`. -/
theorem dropParent_parses : statementOf (sql r"DROP TABLE p;") = dropParent := rfl

/-- With foreign keys off, the drop of the parent resolves to a drop of position 0 without rules. -/
theorem drop_resolves_plain : resolvesTo start dropParent (.drop [0] none) = true := by decide +kernel

/-- With foreign keys on, the same drop resolves to a drop with rules. -/
theorem drop_resolves_with_rules : resolvesWith enforcing dropParent (fun
    | .drop _ (some _) => true
    | _ => false) = true := by
  decide +kernel

/-- Frame law of DROP TABLE with foreign keys off: the child is found by its name at position 0 after the drop of
the parent that stood before it, with the rows that it had at position 1. Proof sketch:
{name}`runScriptStep_dropTable_frame`; the kernel shows that the step continues and that the child had its three
rows at position 1. -/
theorem drop_off_keeps_the_child : ∀ output next others, stepOf start dropParent = .continued output next others →
    foundRows next.state.database (name! "c") =
      some (0, [(10, [.integer 10, .integer 1, .text [97]]), (11, [.integer 11, .integer 2, .text [98]]),
        (12, [.integer 12, .integer 2, .text [99]])]) := by
  intro output next others step
  obtain ⟨after, found⟩ := resolvesTo_sound drop_resolves_plain
  obtain ⟨table, present⟩ := tableNamed_exists (database := start.state.database) (name := name! "c") (position := 1)
    (by decide +kernel)
  have kept := runScriptStep_dropTable_frame (connection := start) (dropped := name! "p") (ifExists := false) rfl found
    step (other := name! "c") (by decide +kernel) present
  have rows := start_rows.2
  unfold foundRows at rows ⊢
  rw [present] at rows
  have moved : keptBelow [0] 1 = 0 := by decide +kernel
  rw [kept, moved]
  simpa using rows

/-- Success law of DROP TABLE with foreign keys off: the database after is the database without the dropped
table and its rows. Proof sketch: {name}`runScriptStep_drop_plain`. -/
theorem drop_off_removes_the_parent : ∀ output next others, stepOf start dropParent = .continued output next others →
    output.isError = false ∧ others = [] ∧ foundRows next.state.database (name! "p") = none := by
  intro output next others step
  obtain ⟨after, found⟩ := resolvesTo_sound drop_resolves_plain
  obtain ⟨noError, single, nextEq⟩ := runScriptStep_drop_plain found step
  refine ⟨noError, single, ?_⟩
  rw [nextEq]
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

-- CREATE TABLE

/-- The statement that creates the table {lit}`q` beside the parent and the child. -/
def createQ : Syntax.Statement := statementOf (sql r"CREATE TABLE q(id INTEGER PRIMARY KEY, v TEXT);")

/-- The statement that creates a table with the name of the parent. -/
def createP : Syntax.Statement := statementOf (sql r"CREATE TABLE p(id INTEGER);")

/-- Whether a statement resolves, on a connection, to a CREATE TABLE of the name at the position. -/
def createsAt (connection : Connection) (statement : Syntax.Statement) (position : Nat) (name : Identifier) : Bool :=
  match resolveStatement runContext connection.resolveState statement with
  | .ok (.createTable target created _, _) => target == position && created == name
  | _ => false

/-- If a statement creates the table of the name at the position, it resolves to that CREATE TABLE. Proof sketch:
invert the match. -/
theorem createsAt_sound {connection : Connection} {statement : Syntax.Statement} {position : Nat} {name : Identifier}
    (checked : createsAt connection statement position name = true) :
    ∃ table after, resolveStatement runContext connection.resolveState statement =
      .ok (.createTable position name table, after) := by
  unfold createsAt at checked
  split at checked
  · rename_i target created table after same
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨rfl, rfl⟩ := checked
    exact ⟨table, after, same⟩
  · cases checked

/-- The statement {lean}`createQ` creates the table {lit}`q` at position 2. -/
theorem createQ_resolves : createsAt start createQ 2 (name! "q") = true := by decide +kernel

/-- Success and frame law of CREATE TABLE: the new table is appended at position 2, the catalog and the row lists
keep their alignment, and the parent and the child are found at their positions with their rows. Proof sketch:
{name}`runScriptStep_createTable` and {name}`runScriptStep_createTable_frame` with the resolution of the statement as
a CREATE TABLE at position 2. -/
theorem create_appends_and_keeps : ∀ output next others, stepOf start createQ = .continued output next others →
    output.isError = false ∧ next.state.database.catalog.length = 3 ∧ next.state.database.rows.length = 3 ∧
    foundRows next.state.database (name! "p") = foundRows start.state.database (name! "p") ∧
    foundRows next.state.database (name! "c") = foundRows start.state.database (name! "c") := by
  intro output next others step
  obtain ⟨table, after, found⟩ := createsAt_sound createQ_resolves
  obtain ⟨noError, -, target, aligned, nextEq⟩ := runScriptStep_createTable found step
  have frame (name : Identifier) (position : Nat) (existing : Table)
      (present : start.state.database.tableNamed name = some (position, existing)) :
      next.state.database.tableNamed name = some (position, existing) :=
    runScriptStep_createTable_frame found step present
  refine ⟨noError, ?_, ?_, ?_, ?_⟩
  · rw [nextEq]; simpa [Catalog.createTable] using (by decide +kernel : start.state.database.catalog.length = 2)
  · rw [nextEq]; simpa using (by decide +kernel : start.state.database.rows.length = 2)
  · obtain ⟨existing, present⟩ := tableNamed_exists (database := start.state.database) (name := name! "p")
      (position := 0) (by decide +kernel)
    unfold foundRows
    rw [frame _ _ _ present, present]
  · obtain ⟨existing, present⟩ := tableNamed_exists (database := start.state.database) (name := name! "c")
      (position := 1) (by decide +kernel)
    unfold foundRows
    rw [frame _ _ _ present, present]

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

/-- Failure law of CREATE TABLE: a CREATE TABLE of a name in use fails with an error output, and the step changes
nothing: the connection after it is the connection before. The kernel shows that the step fails. Proof sketch:
{name}`runScriptStep_createTable_failed`. -/
theorem create_existing_keeps_the_connection : outputOf start createP = some (.error 1) ∧
    ∀ output next others, stepOf start createP = .continued output next others →
      output.isError = true → others = [] ∧ next = start := by
  refine ⟨by decide +kernel, fun output next others step failed => ?_⟩
  obtain ⟨created, columns, constraints, options, form⟩ : ∃ created columns constraints options,
      createP = .createTable created columns constraints options := ⟨_, _, _, _, rfl⟩
  rw [form] at step
  exact runScriptStep_createTable_failed step failed

/-- Failure law of DROP TABLE with foreign keys off: the drop of a table that does not exist fails and changes
nothing. Proof sketch: {name}`runScriptStep_dropTable_off_failed`. -/
theorem drop_missing_keeps_the_connection :
    outputOf start (.dropTable (name! "zz") false) = some (.error 1) ∧
    ∀ output next others, stepOf start (.dropTable (name! "zz") false) = .continued output next others →
      output.isError = true → others = [] ∧ next = start := by
  refine ⟨by decide +kernel, fun output next others step failed => ?_⟩
  exact runScriptStep_dropTable_off_failed (connection := start) (by decide +kernel) step failed

-- DROP TABLE with foreign keys on

/-- Premise of the frame law of DROP TABLE: with foreign keys on, dropping the parent deletes the rows of the child
by the cascade. The child is found by its name at position 0 after the drop, with no rows, so the frame law does not
hold without the premise that foreign keys are off. Proof sketch: kernel evaluation of the step. -/
theorem drop_on_cascades_into_the_child : ∀ output next others, stepOf enforcing dropParent = .continued output next others →
    foundRows next.state.database (name! "c") = some (0, []) := by
  intro output next others step
  have kernel : (afterStep enforcing dropParent).map (fun after => foundRows after.state.database (name! "c")) =
      some (some (0, [])) := by decide +kernel
  rw [afterStep_of_continued step] at kernel
  simpa using kernel

/-- With foreign keys on, the drop of the parent resolves to a drop of position 0 with rules. -/
def dropsWithRules (connection : Connection) (statement : Syntax.Statement) (positions : List Nat) : Bool :=
  match resolveStatement runContext connection.resolveState statement with
  | .ok (.drop dropped (some _), _) => dropped == positions
  | _ => false

/-- If a statement drops the positions with rules, it resolves to that drop. Proof sketch: invert the match. -/
theorem dropsWithRules_sound {connection : Connection} {statement : Syntax.Statement} {positions : List Nat}
    (checked : dropsWithRules connection statement positions = true) :
    ∃ rules after, resolveStatement runContext connection.resolveState statement =
      .ok (.drop positions (some rules), after) := by
  unfold dropsWithRules at checked
  split at checked
  · rename_i dropped rules after same
    simp only [beq_iff_eq] at checked
    subst checked
    exact ⟨rules, after, same⟩
  · cases checked

/-- The success law of DROP TABLE with foreign keys on is the law of the key run: the catalog after is the catalog
without the dropped objects. The rows depend on the actions of the keys, which is why the law names the key run and
not the rows. Proof sketch: {name}`runScriptStep_drop_keys` with the resolution of the drop with rules. -/
theorem drop_on_removes_the_parent_from_the_catalog : ∀ output next others,
    stepOf enforcing dropParent = .continued output next others → output.isError = false →
      next.state.database.catalog = enforcing.state.database.catalog.drop [0] := by
  intro output next others step noError
  obtain ⟨rules, after, found⟩ := dropsWithRules_sound (positions := [0]) (by decide +kernel : dropsWithRules enforcing dropParent [0] = true)
  obtain ⟨_, _, _, catalogEq, _⟩ := runScriptStep_drop_keys found step noError
  exact catalogEq

#print axioms drop_off_keeps_the_child
#print axioms drop_off_removes_the_parent
#print axioms create_appends_and_keeps
#print axioms create_existing_keeps_the_connection
#print axioms drop_missing_keeps_the_connection
#print axioms drop_on_cascades_into_the_child
#print axioms drop_on_removes_the_parent_from_the_catalog

end SchemaStepLaws
