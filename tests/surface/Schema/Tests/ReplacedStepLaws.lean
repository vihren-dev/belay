import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule
import Belay.Sqlite.Model.Programs.Scripts.ResolvedStepGuards
import Belay.Sqlite.Model.Programs.Scripts.NonQueryOutput
import Belay.Sqlite.Model.Schema.Ddl.TableByName
import Belay.Sqlite.Model.Schema.Ddl.SchemaExtensionLaws

/-! A fixture module of {lit}`tests/surface_schema_script_test.py` (statement rule pilot, "No capability loss"). The
pilot deleted seven model laws about the step of CREATE TABLE and of INSERT. Each theorem of this module has the
name and the statement of one deleted law, with its binders and premises from the revision before the pilot. The
proofs use the kind rules {name}`runScriptStep_createTable_eq` and {name}`runScriptStep_plainInsert_eq`. They also
use the data facts of {name}`Database.createTable` and {name}`insertOutcome` and the laws that serve all kinds. When
a theorem does not compile, the new form has lost the fact. -/

set_option doc.verso true

namespace Belay.Sqlite.Model.ReplacedStepLaws

/-- The deleted law {lit}`runScriptStep_createTable`. For every connection and statement that resolves to a CREATE
TABLE, and every step that continues: the output is not an error, there is no further execution, the target is
the end of the catalog, the rows are aligned with the catalog, and the next connection is the connection with the
table and an empty row list appended and nothing else changed. The law has no validity premise: the guard facts
come from the step that continues. Proof sketch: the kind rule gives the step; the branch that ends contradicts
the step, and the branch that continues gives each conjunct. -/
theorem runScriptStep_createTable {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {target : Nat} {name : Identifier} {table : CatalogTable}
    (found : resolveStatement context connection.resolveState statement = .ok (.createTable target name table, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      target = connection.state.database.catalog.length ∧
      connection.state.database.rows.length = connection.state.database.catalog.length ∧
      next = { connection with state := { connection.state with database :=
        { catalog := connection.state.database.catalog.createTable name table,
          rows := connection.state.database.rows ++ [[]] } } } := by
  rw [runScriptStep_createTable_eq found] at step
  split at step
  · rename_i guard
    cases step
    exact ⟨rfl, rfl, guard.1, guard.2, rfl⟩
  · cases step

/-- The deleted law {lit}`runScriptStep_createTable_frame`. For every connection, statement that resolves to a
CREATE TABLE and step that continues, and every name that finds a table in the database of the connection: the
name finds the same table, with the same rows, at the same position in the database of the next connection.
Proof sketch: the kind rule gives the next database, and {name}`Database.tableNamed_createTable` the lookup. -/
theorem runScriptStep_createTable_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {target : Nat} {created : Identifier} {definition : CatalogTable}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.createTable target created definition, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    {name : Identifier} {position : Nat} {table : Table}
    (present : connection.state.database.tableNamed name = some (position, table)) :
    next.state.database.tableNamed name = some (position, table) := by
  rw [runScriptStep_createTable_eq found] at step
  split at step
  · cases step
    exact Database.tableNamed_createTable present created definition
  · cases step

/-- The deleted law {lit}`runScriptStep_createTable_empty`. Whenever a resolved CREATE TABLE step continues, the
new position holds the resolved table shape with no rows. Proof sketch: the guard of the kind rule gives the end
position and the aligned rows, and {name}`Database.table_createTable_end` the empty table there. -/
theorem runScriptStep_createTable_empty {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {c next : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {pos : Nat} {name : Identifier} {shape : CatalogTable} {out : Output} {others : List StatementExecution}
    (resolved : resolveStatement context c.resolveState statement = .ok (.createTable pos name shape, after))
    (step : runScriptStep context clock index c statement parameters = .continued out next others) :
    next.state.database.table pos = some ⟨shape, []⟩ := by
  rw [runScriptStep_createTable_eq resolved] at step
  split at step
  · rename_i guard
    obtain ⟨rfl, aligned⟩ := guard
    cases step
    exact Database.table_createTable_end name shape aligned
  · cases step

/-- The deleted law {lit}`runScriptStep_createTable_ok`. On every valid database, if resolution gives a CREATE
TABLE, its step continues once with a successful output. Proof sketch: {name}`step_guards_hold` gives the guard
of the kind rule, so the rule selects the branch that continues. -/
theorem runScriptStep_createTable_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {name : Identifier} {table : CatalogTable} {profile : Profile}
    (found : resolveStatement context connection.resolveState statement = .ok (.createTable target name table, after))
    (valid : connection.state.database.Valid profile) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  have guards := step_guards_hold found rfl valid
  simp only [Resolved.Statement.StepGuards] at guards
  rw [runScriptStep_createTable_eq found]
  simp only [guards, and_self, ↓reduceIte]
  exact ⟨_, _, rfl, rfl⟩

/-- The deleted law {lit}`plainInsert_database`. For every connection, plain insert without subqueries and
error-free step that continues: the next connection has the database with the rows that
{name}`LiteralData.inserted` gives, stored at the target, for the clock value of the step. Proof sketch: split the
kind rule; each branch that ends contradicts the step, and the failure branch contradicts the output without
error. -/
theorem plainInsert_database {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {target : Nat} {cells : List (List Resolved.Cell)} {after : ResolveState} {table : Table}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insert target cells [] [] none, after))
    (present : connection.state.database.table target = some table)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ value : Int, statementClock clock index (.insert target cells [] [] none) = some value ∧
      next.state.database = connection.state.database.setRows target
        (LiteralData.inserted table (Resolved.rowsAt (Resolved.statementContext value
          (connection.state.counters.view (Resolved.Statement.insert target cells [] [] none).counterReads)
          parameters connection.state.database []) table.shape.columns cells)).rows := by
  rw [runScriptStep_plainInsert_eq found] at step
  split at step
  · cases step
  · rename_i value timed
    refine ⟨value, timed, ?_⟩
    dsimp only at step
    split at step
    · cases step
    · simp only [present] at step
      split at step
      · split at step
        · cases step
          rfl
        · cases step
          simp [Output.isError] at noError
      · cases step

/-- The deleted law {lit}`runScriptStep_insert_ne_oneOf`. For every connection, statement that resolves to an
insert (with or without a RETURNING clause and write rules), and step that continues: the output of the step is
not a choice between results. Proof sketch: an insert is not a query, so
{name}`runScriptStep_ne_oneOf_of_not_query` applies. -/
theorem runScriptStep_insert_ne_oneOf {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution} {target : Nat}
    {cells : List (List Resolved.Cell)} {returning subqueries rules} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insert target cells returning subqueries rules, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (alternatives : List (List (List Value))) : output ≠ .oneOf alternatives :=
  runScriptStep_ne_oneOf_of_not_query found (fun _ _ same => by cases same) step alternatives

/-- The deleted law {lit}`runScriptStep_insert_ok`. If a statement resolves to a plain INSERT without RETURNING or
write rules, {name}`statementClock` gives a value for it, each counter that it reads is known, its target holds a
table, its subqueries are plain, its cell expressions are ready and the values satisfy {name}`InsertFits`, then the
step continues once with the inserted row count and no further execution. The database of its next connection is
{name}`Database.setRows` of the target and the rows of {name}`LiteralData.inserted`. These rows are the old rows
followed by the new rows. When the target has no row store, that database is the database before. The next
connection applies the insertion counts. Proof sketch: the premises select the success branch of the kind rule; {name}`insertReady_of_fits` and {name}`insertOutcome_of_fits` give the readiness
check and the outcome. -/
theorem runScriptStep_insert_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)} {subqueries : List Resolved.Query} {value : Int} {table : Table}
    (found : resolveStatement context connection.resolveState statement = .ok (.insert target rows [] subqueries none, after))
    (timed : statementClock clock index (.insert target rows [] subqueries none) = some value)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.insert target rows [] subqueries none).counterReads = none)
    (located : connection.state.database.table target = some table) (plain : Resolved.subqueriesPlain subqueries = true) :
    let resolved := Resolved.Statement.insert target rows [] subqueries none
    let counters := connection.state.counters.view resolved.counterReads
    let eval := Resolved.statementContext value counters parameters connection.state.database subqueries
    let values := Resolved.rowsAt eval table.shape.columns rows
    let written := connection.state.database.setRows target (LiteralData.inserted table values).rows
    let keys := connection.state.database.keys target table
    Resolved.cellsReady eval rows = true → InsertFits keys table values →
      runScriptStep context clock index connection statement parameters =
        .continued (.done rows.length) (connection.afterWrite written (LiteralData.insertCounts (.ok written) keys table values)) [] := by
  dsimp only
  intro ready fits
  rw [runScriptStep_plainInsert_eq found]
  simp only [timed, known, located]
  rw [insertReady_of_fits fits, plain, ready, insertOutcome_of_fits fits]
  rfl

#print axioms runScriptStep_createTable
#print axioms runScriptStep_createTable_frame
#print axioms runScriptStep_createTable_empty
#print axioms runScriptStep_createTable_ok
#print axioms plainInsert_database
#print axioms runScriptStep_insert_ne_oneOf
#print axioms runScriptStep_insert_ok

end Belay.Sqlite.Model.ReplacedStepLaws
