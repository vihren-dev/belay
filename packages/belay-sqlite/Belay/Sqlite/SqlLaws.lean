import Belay.Sqlite.SqlExecution
import Belay.Sqlite.Resolution.StatementCatalog

set_option doc.verso true

/-! Schema-only proof laws for the full SQL executor. Keeping these guarded
conveniences separate leaves the statement and transaction semantics in one module. -/

namespace Belay.Sqlite

/-- For every database, position, reason and result database, the failure of an idle
state is the plain failure. Proof sketch: without a snapshot both branches of the reason
test finish to the failure itself. -/
@[simp] theorem SqlState.failed_idle (current : Database) (position : Nat) (reason : ExecutionError)
    (database : Database) : ({ database := current } : SqlState).failed position reason database =
      .failure position reason database := by
  unfold SqlState.failed SqlState.finish
  split <;> rfl

/-- The error of an outcome: the reason of a failure, the error of a pending result, or
none. -/
def Outcome.error? : Outcome → Option ExecutionError
  | .success _ => none
  | .failure _ reason _ => some reason
  | .pending _ _ error => error.map (·.2)

/-- For every state, position, reason and database, the error of
{name}`SqlState.failed` is the reason. Proof sketch: split on the ROLLBACK test and the
snapshot; each branch is the failure, or the pending result that carries its reason. -/
theorem SqlState.failed_error (state : SqlState) (position : Nat) (reason : ExecutionError) (database : Database) :
    (state.failed position reason database).error? = some reason := by
  unfold SqlState.failed SqlState.finish
  split <;> (try split) <;> (try split) <;> simp_all [Outcome.error?]

/-- For every state, position, reason other than ROLLBACK and database:
{name}`SqlState.failed` has that database as its visible database, and the saved snapshot
when present, or else that database, as its persisted database. Proof sketch: the
ROLLBACK test fails, so the result is {name}`SqlState.finish` of the failure; split on the
snapshot. -/
theorem SqlState.failed_database (state : SqlState) (position : Nat) (reason : ExecutionError) (database : Database)
    (other : reason ≠ .constraintRollback) :
    (state.failed position reason database).database = database ∧
    (state.failed position reason database).persistedDatabase = state.snapshot.getD database := by
  unfold SqlState.failed
  split
  · contradiction
  · cases h : state.snapshot <;> simp [SqlState.finish, h, Outcome.database, Outcome.persistedDatabase]

/-- For every state, position and database: {name}`SqlState.failed` of a ROLLBACK
failure has the saved snapshot when present, or else that database, as its visible and
its persisted database. Proof sketch: the ROLLBACK test holds; split on the snapshot,
which gives the failure over the snapshot or the finished failure. -/
theorem SqlState.failed_rollback (state : SqlState) (position : Nat) (database : Database) :
    (state.failed position .constraintRollback database).database = state.snapshot.getD database ∧
    (state.failed position .constraintRollback database).persistedDatabase = state.snapshot.getD database := by
  unfold SqlState.failed
  split
  · cases h : state.snapshot <;> simp [SqlState.finish, h, Outcome.database, Outcome.persistedDatabase]
  · contradiction

/-- Every statement in the script is CREATE TABLE or ADD COLUMN. This is a syntax
guard, not a validity or success claim. The empty script satisfies it; CREATE
INDEX, transaction control, literal writes and prepare errors do not. Use it for
schema preservation laws. -/
def SchemaOnly (script : List Resolved.Statement) : Prop :=
  ∀ statement ∈ script, statement.kind = .definition

/-- No statement in the script is INSERT (with or without {lit}`ON CONFLICT`, or with
cells that read the clock), UPDATE or DELETE, and no query has a JSON call in its expressions
({name}`Resolved.Query.expressions`, {name}`Resolved.Expr.isJsonCall` at any depth) or a {lit}`json_each`
source. This is a syntax guard, not a success claim; the empty script satisfies it. Each
statement:
* is not a write ({name}`Resolved.Statement.Kind.write`), and
* if it is a query, has no JSON call and no {lit}`json_each` source. -/
def NoWrites (script : List Resolved.Statement) : Prop :=
  ∀ statement ∈ script, statement.kind ≠ .write ∧ ∀ query, statement = .query query →
    query.expressions.all (!·.any Resolved.Expr.isJsonCall) = true ∧ query.sources.all (!·.source.isEach) = true

/-- Each definition in the script is one that the model describes: each CREATE
TABLE creates a {name}`CatalogTable.plain` table, each ADD COLUMN has a time default
({name}`CatalogColumn.clockDefault`) or a successful {name}`readDefaultValue` result, and no
statement is CREATE INDEX. Other
statements are unrestricted; the empty script satisfies it. -/
def ModeledDefinitions (script : List Resolved.Statement) : Prop :=
  ∀ statement ∈ script, match statement with
    | .createTable _ _ table => table.plain = true
    | .addColumn _ column => (column.clockDefault || (readDefaultValue column).toOption.isSome) = true
    | .createIndex .. => False
    | .insert .. | .upsert .. | .update .. | .delete .. | .begin | .commit | .rollback | .prepareError _
    | .query _ => True

/-- For every position and connection state, a {name}`NoWrites` script with
{name}`ModeledDefinitions` passes the reached-statement support check, because
only writes and queries have a data check, and a query without a JSON call passes it. The proof inducts over the script and follows
each actual transition. -/
theorem supportedSqlFrom_noWrites (guard : NoWrites script) (modeled : ModeledDefinitions script) :
    supportedSqlFrom position script state = true := by
  induction script generalizing position state with
  | nil => rfl
  | cons statement rest ih =>
    have first := guard statement (by simp)
    have firstModeled := modeled statement (by simp)
    have tail : NoWrites rest := fun item member => guard item (by simp [member])
    have tailModeled : ModeledDefinitions rest := fun item member => modeled item (by simp [member])
    have ready : statementReady (state.clock position) statement state.database = true := by
      cases statement with
      | query query =>
        obtain ⟨plain, noEach⟩ : (query.expressions.all fun x => !x.any Resolved.Expr.isJsonCall) = true ∧
            query.sources.all (!·.source.isEach) = true := first.2 query rfl
        simp only [statementReady]
        cases found : query.source (state.clock position) state.database with
        | none => rfl
        | some source =>
          have clean := Resolved.source_fault_of_plain _ state.database query.sources _ source noEach rfl found
          by_cases must : query.mustFail (state.clock position) source.rows = true <;>
            simp [Resolved.Query.run, Resolved.Query.mayFail_of_plain _ query _ plain, clean, must]
      | createTable | createIndex | addColumn | begin | commit | rollback | insert | upsert | update | delete
      | prepareError => simp_all [statementReady]
    simp only [supportedSqlFrom, ready, Bool.true_and]
    cases advance position statement state with
    | halt outcome => rfl
    | next next => exact ih tail tailModeled

/-- For every position and connection state, a {name}`SchemaOnly` script with
{name}`ModeledDefinitions` passes the reached-statement support check. It
follows from {name}`supportedSqlFrom_noWrites`, because a schema-only script has
no writes. -/
theorem supportedSqlFrom_schemaOnly (guard : SchemaOnly script) (modeled : ModeledDefinitions script) :
    supportedSqlFrom position script state = true :=
  supportedSqlFrom_noWrites (fun statement member => by
    have first := guard statement member
    cases statement <;> simp_all) modeled

/-- For every clock value, statement, database, reason and kept database: if {name}`step`
fails with the reason and the kept database, the kept database is the input database.
Proof sketch: every error branch of {name}`step` keeps its input. -/
theorem step_error_keeps {clock : Int} {statement : Resolved.Statement} {database kept : Database}
    {reason : ExecutionError} (failed : step clock statement database = .error (reason, kept)) : kept = database := by
  cases statement <;> simp only [step] at failed
  all_goals (repeat' split at failed)
  all_goals first | (cases failed; rfl) | cases failed

/-- For every position and idle database, a guarded schema statement uses the
primitive transition: success continues with the result, and an error halts with the
error at the position over the input database. The proof splits on the statement, uses
the guard to exclude transaction control and literal-write constructors, and
{name}`step_error_keeps` for the database of an error. -/
theorem advance_schemaOnly
    (guard : SchemaOnly [statement]) :
    advance position statement { database := database } =
      match step 0 statement database with
      | .ok result => .next { database := result }
      | .error (reason, _) => .halt (.failure position reason database) := by
  have first := guard statement (by simp)
  have literal : literalStep 0 statement database = step 0 statement database := by
    cases statement <;> simp_all [literalStep]
  have control : statement.isControl = false := by cases statement <;> simp_all [Resolved.Statement.isControl]
  have ordinary : advance position statement { database := database } =
      ({ database := database } : SqlState).publish position (step 0 statement database) := by
    cases statement <;> simp_all [advance, Resolved.Statement.isControl]
  rw [ordinary]
  cases stepped : step 0 statement database with
  | ok result => rfl
  | error failure =>
    obtain ⟨reason, kept⟩ := failure
    have same := step_error_keeps stepped
    subst same
    simp [SqlState.publish]

/-- For every idle starting database and position, appending a suffix to a
{name}`SchemaOnly` prefix resumes at its next position after success and retains
its stopped error otherwise. The prefix cannot open a transaction. This law does
not describe transaction prefixes; their EOF pending state must be resumed with
its committed snapshot. The proof inducts over primitive schema transitions. -/
theorem runSqlFrom_schemaOnly_append (guard : SchemaOnly initial) :
    runSqlFrom position (initial ++ suffix) { database := database } =
      match runSqlFrom position initial { database := database } with
      | .success result => runSqlFrom (position + initial.length) suffix { database := result }
      | .failure index reason result => .failure index reason result
      | .pending persisted visible error => .pending persisted visible error := by
  induction initial generalizing database position with
  | nil => simp [runSqlFrom, SqlState.finish]
  | cons statement rest ih =>
    have first : SchemaOnly [statement] := fun item member => by
      simp only [List.mem_singleton] at member
      subst item
      exact guard statement (by simp)
    have tail : SchemaOnly rest := fun item member => guard item (by simp [member])
    simp only [List.cons_append, runSqlFrom, advance_schemaOnly first]
    cases executed : step 0 statement database with
    | error failure => rfl
    | ok result => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih tail (database := result) (position := position + 1))

/-!
```lean
example : Belay.Sqlite.SchemaOnly [] := by
  intro statement member
  simp at member
example : ¬ Belay.Sqlite.SchemaOnly [Belay.Sqlite.Resolved.Statement.begin] := by
  intro guard
  exact absurd (guard .begin (by simp)) (by decide)
```
-/

end Belay.Sqlite
