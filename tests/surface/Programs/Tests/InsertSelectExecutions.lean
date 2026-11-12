import Belay

/-! A fixture module of `tests/surface_execution_test.py`: INSERT from a query has one execution for
each order in which SQLite may read its source (ADR 0019, D4), and a claim about the statement is a
claim about all of them. The source table {lit}`s` has an index on {lit}`x`, so a query on {lit}`x`
may be answered by the scan or by the index. The scan gives the rowids 1 and 2 to the values 20 and 10;
the index gives them to 10 and 20, as native SQLite 3.51.0 does for the filter {lit}`x > 0`. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace InsertSelectExecutionExamples
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The source {lit}`s` with the rows (1, 20) and (2, 10), its index on {lit}`x`, and the empty target
{lit}`t` (the third table of the catalog, at position 2). -/
def sample : Belay.Sqlite.Database := db! r"CREATE TABLE s(id INTEGER PRIMARY KEY, x INTEGER);
  CREATE INDEX sx ON s(x);
  CREATE TABLE t(id INTEGER PRIMARY KEY, name INTEGER);
  INSERT INTO s VALUES (1, 20), (2, 10)"

/-- A fresh context without a clock. -/
def start : ExecutionContext :=
  ExecutionContext.initial sample { clock := none, counters := Counters.newConnection }

/-- A fresh context on a database without tables. -/
def emptyStart : ExecutionContext :=
  ExecutionContext.initial Belay.Sqlite.Database.empty { clock := none, counters := Counters.newConnection }

/-- The copy of the values of {lit}`x` into {lit}`t`. -/
def copy : Sql (List Output) := send (sql r"INSERT INTO t(name) SELECT x FROM s WHERE x > 0")

/-- The names in the rows of {lit}`t` in scan order. -/
def names (state : ExecutionContext) : List Value :=
  (state.connection.state.database.rowsAt 2).map (·.values.getD 1 .null)

/-- The claim that holds for each execution: the copy succeeds, and {lit}`t` holds the two values in
some order. -/
theorem every_execution_has_both_values :
    copy.andOk (fun _ state => names state = [.integer 20, .integer 10] ∨ names state = [.integer 10, .integer 20])
      start := by decide +kernel

/-- A claim about the order of the rows is false: the execution that reads the index gives the rowid 1
to the value 10, so "the first row holds 20" does not hold for every execution. -/
theorem first_row_claim_fails :
    ¬ copy.andOk (fun _ state => (names state).head? = some (.integer 20)) start := by decide +kernel

/-- The claim that the first row holds 20 is not refuted by the model's own execution alone: the
claim for the execution that reads the scan holds, so the failure above is due to the other
execution. The claim over the weaker postcondition "the first row holds 20 or 10" holds. -/
theorem first_row_is_a_value :
    copy.andOk (fun _ state => (names state).head? = some (.integer 20) ∨ (names state).head? = some (.integer 10))
      start := by decide +kernel

set_option sql.orderWarnings false in
/-- A script in which one execution fails and the other succeeds. The source rows are 5 and the smallest
integer. The scan reaches 5 and stops at the limit. The index reaches the smallest integer first, and
{lit}`abs` of it is an integer overflow (native SQLite 3.51.0 gives both results). -/
def limited : Sql (List Output) :=
  send (sql r"CREATE TABLE s(id INTEGER PRIMARY KEY, x INTEGER);
    CREATE INDEX sx ON s(x);
    CREATE TABLE t(id INTEGER PRIMARY KEY);
    INSERT INTO s VALUES (1, 5), (2, -9223372036854775808);
    INSERT INTO t SELECT abs(x) FROM s WHERE x < 100 LIMIT 1")

/-- The script does not succeed: one of its executions ends with an error. -/
theorem some_execution_fails :
    ¬ limited.SucceedsFrom none 0 emptyStart.connection := by
  decide +kernel

/-- The copy without a limit succeeds in every execution. -/
theorem copy_succeeds : copy.SucceedsFrom none 0 start.connection := by decide +kernel

/-- The parsed copy step, reused to inspect every reached connection. -/
def copyStatement : Syntax.Statement := (sql r"INSERT INTO t(name) SELECT x FROM s WHERE x > 0").statements[0].1

/-- A later query reads a clock, one counter and one bound parameter. -/
def inputStatement : Syntax.Statement :=
  (sql r"SELECT CURRENT_TIMESTAMP, total_changes(), ?1" (Value.integer 42)).statements[0].1

/-- At position seven the supplied clock gives 17, independently of the connection's clock. -/
def inputClock : Option Clock := some fun index => index + 10

/-- The actual two copy executions, starting at a nonzero position. -/
def copied : RunStep := runScriptStep runContext inputClock 6 start.connection copyStatement []

/-- The copy has no extra obligation. The later query requires the selected inputs and either
of the two reached row orders. The full counter record differs from this visible view. -/
def nextInputs : StatementCondition := fun value counters parameters statement database =>
  if statement.fromQuery then True else
    value = 17 ∧ counters = { totalChanges := some 2 } ∧ parameters = [.integer 42] ∧
      (database.rowsAt 2).map (·.values.getD 1 .null) ∈
        [[.integer 20, .integer 10], [.integer 10, .integer 20]]

/-- Both real branches supply their own database and counters to the later condition.
Proof sketch: compute both reached states, then use each resolution and clock equation. -/
theorem reached_inputs : ∀ execution ∈ copied.executions,
    ScriptStepCondition nextInputs runContext inputClock 7 execution.next inputStatement [.integer 42] := by
  have facts : ∀ execution ∈ copied.executions,
      execution.next.resolveState = start.connection.resolveState ∧
      execution.next.state.counters = { changes := some 2, totalChanges := some 2, lastInsertRowid := some 2 } ∧
      (execution.next.state.database.rowsAt 2).map (·.values.getD 1 .null) ∈
        [[.integer 20, .integer 10], [.integer 10, .integer 20]] := by decide +kernel
  intro execution member resolved after value found selected _
  obtain ⟨same, counters, rows⟩ := facts execution member
  rw [same] at found
  change Except.ok _ = Except.ok (resolved, after) at found
  cases found
  change some 17 = some value at selected
  cases selected
  exact ⟨rfl, by rw [counters]; rfl, rfl, rows⟩

/-- The common predicate follows each branch's later obligation, with no support premise added
at the script entry. Proof sketch: the copy resolves to INSERT SELECT, and each of its next states
meets {name}`reached_inputs`; both suffixes are empty. -/
theorem branch_conditions : ScriptConditionsWith Model.Database.RowsShaped nextInputs runContext inputClock 6
    start.connection [(copyStatement, []), (inputStatement, [.integer 42])] := by
  refine ⟨?_, ?_⟩
  · intro _ resolved after _ found _ _
    change Except.ok _ = Except.ok (resolved, after) at found
    cases found
    trivial
  · intro execution member
    refine ⟨fun _ => reached_inputs execution member, ?_⟩
    split
    · trivial
    · exact fun _ _ => trivial

/-- The shared all-execution preservation law handles a divergent INSERT SELECT and each later
input-dependent obligation. Proof sketch: specialize rows-shape evidence and apply {name}`branch_conditions`. -/
theorem branch_preservation : ∀ run ∈ runScriptAllFrom runContext inputClock 6 start.connection
    [(copyStatement, []), (inputStatement, [.integer 42])], run.connection.state.Holds Model.Database.RowsShaped :=
  runScriptAllFrom_holds (condition := nextInputs)
    (fun clock counters parameters statement database holds _ =>
      rowsShaped_statementKeeps clock counters parameters statement database holds trivial)
    runContext inputClock 6 _ ⟨sample.valid.admitted.rowsShaped, fun _ impossible => nomatch impossible⟩ branch_conditions

/-- Checking only the canonical branch's row order cannot discharge the later obligations.
Proof sketch: select the other actual execution and specialize its query obligation. -/
theorem other_branch_required : ¬ ScriptConditionsWith (fun _ => True)
    (fun _ _ _ statement database => statement.fromQuery = true ∨
      ((database.rowsAt 2).map (·.values.getD 1 .null)).head? = some (.integer 20))
    runContext inputClock 6 start.connection [(copyStatement, []), (inputStatement, [.integer 42])] := by
  intro met
  have later := met.2
  change ∀ execution ∈ [_, _], _ at later
  have alternative := later _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have required := alternative.1 ⟨trivial, fun _ _ => trivial⟩ _ _ 17 rfl rfl rfl
  change false = true ∨ some (Value.integer 10) = some (.integer 20) at required
  simp at required

/-- A missing selected clock ends execution; even a false condition is unnecessary at that step
and throughout its suffix. Proof sketch: resolution selects a clock-reading query, which has no clock value. -/
theorem missing_clock_ends_obligations : ScriptConditionsWith (fun _ => True)
    (fun _ _ _ _ _ => False) runContext none 7 start.connection
    [(inputStatement, [.integer 42]), (copyStatement, [])] := by
  refine ⟨?_, trivial⟩
  intro _ resolved after value found selected _
  change Except.ok _ = Except.ok (resolved, after) at found
  cases found
  contradiction

#print axioms every_execution_has_both_values
#print axioms first_row_claim_fails
#print axioms first_row_is_a_value
#print axioms some_execution_fails
#print axioms copy_succeeds
#print axioms reached_inputs
#print axioms branch_conditions
#print axioms branch_preservation
#print axioms other_branch_required
#print axioms missing_clock_ends_obligations

end InsertSelectExecutionExamples
