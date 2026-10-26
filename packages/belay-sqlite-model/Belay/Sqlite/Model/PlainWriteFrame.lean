import Belay.Sqlite.Model.PlainInsertEffect
import Belay.Sqlite.Model.PlainUpdateEffect

set_option doc.verso true

/-!
What one plain write of the model leaves unchanged (ADR 0017, S6). A plain write is a resolved INSERT,
UPDATE or DELETE without trigger and foreign-key rules. A step of a plain write, whether it succeeds or fails,
changes the rows of its target table only: it keeps the open transaction's snapshot, the connection
settings and the single execution of the model, and it keeps the whole database when it fails. A frame
claim about a program of plain writes needs only these facts and the target of each write.
-/

namespace Belay.Sqlite.Model

/-- The target table position of a plain write: a resolved INSERT, UPDATE or DELETE without rules for
triggers and foreign keys. Any other statement, including a write with rules, has none. For example, a
write with a trigger can change a second table, so it has no plain target. -/
def Resolved.Statement.plainWriteTarget : Resolved.Statement → Option Nat
  | .insert target _ _ _ none | .update target _ _ _ _ none | .delete target _ _ _ none => some target
  | .insert _ _ _ _ (some _) | .update _ _ _ _ _ (some _) | .delete _ _ _ _ (some _) => none
  | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .drop .. | .begin
  | .commit | .rollback | .upsert .. | .prepareError _ | .query .. | .setting .. => none

/-- For every database, target, keys, table, supplied rows and result table: a failed write of the
result gives an error that keeps the input database and has the reason
{name}`ExecutionError.constraintViolation` or {name}`ExecutionError.datatypeMismatch`. Proof sketch:
unfold {name}`insertOutcome` and {name}`checkedWrite`; every failing branch states its reason. -/
theorem insertOutcome_error {database : Database} {target : Nat} {keys : List UniqueKey}
    {table : Table} {rows : List (List Value)} {result : Table} {reason : ExecutionError} {reached : Database}
    (failed : insertOutcome database target keys table rows result = .error (reason, reached)) :
    reached = database ∧ (reason = .constraintViolation ∨ reason = .datatypeMismatch) := by
  unfold insertOutcome at failed
  split at failed
  · dsimp only at failed
    split at failed <;> cases failed <;> simp
  · unfold checkedWrite at failed
    split at failed
    · cases failed
    · cases failed; simp

/-- For every database, target, keys and result table: a failed checked write keeps the input database
and has the reason {name}`ExecutionError.constraintViolation`. Proof sketch: unfold
{name}`checkedWrite`. -/
theorem checkedWrite_error {database : Database} {target : Nat} {keys : List UniqueKey} {result : Table}
    {reason : ExecutionError} {reached : Database}
    (failed : checkedWrite database target keys result = .error (reason, reached)) :
    reached = database ∧ reason = .constraintViolation := by
  unfold checkedWrite at failed
  split at failed
  · cases failed
  · cases failed; simp

/-- For every plain write at a target, clock value, counters, parameters and database: the effect of its run
is either a database that holds the same tables except for the rows at the target, or an error whose reason
is neither {name}`ExecutionError.constraintFail` nor {name}`ExecutionError.constraintRollback`. The
error reasons are the three that a plain write gives: an unmodeled table position, a constraint violation
and a datatype mismatch. Proof sketch: case analysis on the three statement forms and on the table at the
target; {name}`insertOutcome_ok`, {name}`insertOutcome_error` and {name}`checkedWrite_error` read the
effect of the checked write. -/
theorem runStatement_plainWrite_effect {statement : Resolved.Statement} {target : Nat}
    (plain : statement.plainWriteTarget = some target) (clock : Int) (counters : Counters)
    (parameters : List Value) (database : Database) :
    (∀ after, (runStatement clock counters parameters statement database).effect = .ok after →
      ∃ rows, after = database.setRows target rows) ∧
    (∀ reason reached, (runStatement clock counters parameters statement database).effect = .error (reason, reached) →
      reason ≠ .constraintFail ∧ reason ≠ .constraintRollback) := by
  cases statement <;> simp only [Resolved.Statement.plainWriteTarget, reduceCtorEq] at plain
  case insert targetAt cells returning subqueries rules =>
    cases rules <;> simp only [Option.some.injEq, reduceCtorEq] at plain
    subst plain
    simp only [runStatement]
    cases present : database.table targetAt with
    | none => simp
    | some table =>
      simp only [StatementRun.withKeys, Option.map_none]
      refine ⟨fun after ok => ⟨_, insertOutcome_ok ok⟩, fun reason reached failed => ?_⟩
      obtain ⟨-, cases⟩ := insertOutcome_error failed
      rcases cases with rfl | rfl <;> simp
  case update targetAt assignments filter returning subqueries rules =>
    cases rules <;> simp only [Option.some.injEq, reduceCtorEq] at plain
    subst plain
    simp only [runStatement]
    cases present : database.table targetAt with
    | none => simp
    | some table =>
      simp only [StatementRun.withKeys, Option.map_none]
      split
      · simp
      · refine ⟨fun after ok => ?_, fun reason reached failed => ?_⟩
        · unfold checkedWrite at ok
          split at ok
          · cases ok; exact ⟨_, rfl⟩
          · cases ok
        · obtain ⟨-, rfl⟩ := checkedWrite_error failed
          simp
  case delete targetAt filter returning subqueries rules =>
    cases rules <;> simp only [Option.some.injEq, reduceCtorEq] at plain
    subst plain
    simp only [runStatement]
    cases present : database.table targetAt with
    | none => simp
    | some table => exact ⟨fun after ok => by cases ok; exact ⟨_, rfl⟩, by simp [StatementRun.withKeys]⟩

/-- For every connection, resolution state that keeps the settings, index, run and a set of permitted
databases that contains the database of the connection: if the effect of the run either gives a permitted
database or fails with a reason other than {name}`ExecutionError.constraintFail` and
{name}`ExecutionError.constraintRollback`, then the connection after the transition of the run is the
connection with a permitted database and with the counters changed by the counts of the run. In plain words,
the snapshot, the clock and the settings stay. Proof sketch: a success publishes the database of the
effect. A failure with an ordinary reason is {name}`SqlState.finish` of a failure that holds the database
of the connection; {name}`Connection.afterError` keeps that database and, with a snapshot, the snapshot. -/
theorem afterStep_frame (connection : Connection) (after : ResolveState) (index : Nat)
    (run : StatementRun) (permitted : Database → Prop) (start : permitted connection.state.database)
    (foreignKeys : after.foreignKeys = connection.foreignKeys)
    (recursiveTriggers : after.recursiveTriggers = connection.recursiveTriggers)
    (okFrame : ∀ database, run.effect = .ok database → permitted database)
    (errorFrame : ∀ reason reached, run.effect = .error (reason, reached) →
      reason ≠ .constraintFail ∧ reason ≠ .constraintRollback) :
    ∃ database, permitted database ∧
      connection.afterStep after run.counts ((connection.state.publish index run.effect).counted run.counts) =
        { connection with state := { connection.state with
            database, counters := connection.state.counters.apply run.counts } } := by
  cases effect : run.effect with
  | ok database =>
    refine ⟨database, okFrame database effect, ?_⟩
    simp [SqlState.publish, SqlTransition.counted, Connection.afterStep, foreignKeys, recursiveTriggers]
  | error failure =>
    obtain ⟨reason, reached⟩ := failure
    obtain ⟨notFail, notRollback⟩ := errorFrame reason reached effect
    refine ⟨connection.state.database, start, ?_⟩
    rcases snapshot : connection.state.snapshot with _ | original <;>
      simp [SqlState.publish, SqlTransition.counted, Connection.afterStep, Connection.afterError,
        SqlState.failed, SqlState.finish, notFail, notRollback, snapshot, foreignKeys, recursiveTriggers]

/-- For every connection, statement that resolves to a plain write at a target, and step that continues: the
step has no other execution than the model's own; the next connection keeps the snapshot and the settings of
the connection; and its database is either the database of the connection, which a failed write leaves
unchanged, or that database with the rows at the target replaced. In plain words, the step cannot change a
table other than the target, the catalog, the open transaction or a setting, whatever the clock, the counters
and the values bound to the parameters. Proof sketch: {name}`runScriptStep_continued_spec` gives the next
connection as {name}`Connection.afterStep` of the transition of the run;
{name}`runStatement_plainWrite_effect` and {name}`afterStep_frame` read it. -/
theorem runScriptStep_plainWrite_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState} {target : Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (plain : resolved.plainWriteTarget = some target)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    others = [] ∧ next.state.snapshot = connection.state.snapshot ∧
      next.foreignKeys = connection.foreignKeys ∧ next.recursiveTriggers = connection.recursiveTriggers ∧
      (next.state.database = connection.state.database ∨
        ∃ rows, next.state.database = connection.state.database.setRows target rows) := by
  obtain ⟨nothing, resolved', after', value, same, -, -, -, -, -, nextEq⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  have ordinary : resolved.isControl = false := by
    cases resolved <;> simp_all [Resolved.Statement.plainWriteTarget, Resolved.Statement.isControl]
  have afterEq := resolveStatement_after context _ _ _ _ found
  rw [ResolveState.after_of_isControl _ ordinary] at afterEq
  obtain ⟨okFrame, errorFrame⟩ := runStatement_plainWrite_effect plain value
    (connection.state.counters.view resolved.counterReads) parameters connection.state.database
  rw [nextEq, advanceRun_ordinary index resolved connection.state _ ordinary]
  have foreignKeys : after.foreignKeys = connection.foreignKeys := by rw [afterEq]; rfl
  have recursiveTriggers : after.recursiveTriggers = connection.recursiveTriggers := by rw [afterEq]; rfl
  obtain ⟨database, permitted, same⟩ := afterStep_frame connection after index (connection.state.statementRun value parameters resolved)
    (fun database => database = connection.state.database ∨
      ∃ rows, database = connection.state.database.setRows target rows) (Or.inl rfl) foreignKeys recursiveTriggers
    (fun database ok => Or.inr (okFrame database ok)) errorFrame
  rw [same]
  exact ⟨nothing, rfl, rfl, rfl, permitted⟩

end Belay.Sqlite.Model
