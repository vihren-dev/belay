import Belay.Sqlite.StepCatalog

set_option doc.verso true

/-! Resolution and execution agree on the catalog. Resolution predicts the catalog after a
script ({lit}`resolve`); execution carries a catalog in its state and changes it with the
same functions. The final theorem {lit}`runSqlAt_catalog` states that a run without an
error ends with the catalog that resolution predicts. -/

namespace Belay.Sqlite

/-- For every script, position, agreeing connection and resolution states, and outcome of
{name}`runSqlFrom` without an error (a success, or a pending transaction without an
error): the catalog of the outcome's visible database is the catalog of the fold of
{name}`ResolveState.after` over the script. An outcome with an error is not covered. Proof
sketch: induction on the script; a halt has an error ({name}`advance_halt_error`), and a
continuing step keeps the states in agreement ({name}`advance_agrees`). -/
theorem runSqlFrom_agrees :
    ∀ (script : List Resolved.Statement) (position : Nat) (sql : SqlState) (state : ResolveState),
      sql.Agrees state → ∀ outcome, runSqlFrom position script sql = outcome → outcome.error? = none →
      outcome.database.catalog = (script.foldl ResolveState.after state).catalog
  | [], position, sql, state, agrees, outcome, run, clean => by
    simp only [runSqlFrom] at run
    subst run
    cases h : sql.snapshot <;> simp [SqlState.finish, h, Outcome.database, agrees.1]
  | statement :: rest, position, sql, state, agrees, outcome, run, clean => by
    simp only [runSqlFrom] at run
    split at run
    · rename_i halted _ halt
      subst run
      have := advance_halt_error halt
      simp [clean] at this
    · rename_i next continued
      exact runSqlFrom_agrees rest (position + 1) next (state.after statement) (advance_agrees agrees continued)
        outcome run clean

/-- For every state, clock value and statement, {name}`ResolveState.after` of the
statement at the clock value ({name}`Resolved.Statement.atClock`) is
{name}`ResolveState.after` of the statement: the clock changes values, not the catalog.
Proof sketch: {name}`ResolveState.after` reads only the constructor and its catalog
fields, and {lit}`expressionsAtClock` and {lit}`fillCells` keep both; a clocked statement
becomes the statement it wraps, whose state is the same. -/
theorem ResolveState.after_atClock (state : ResolveState) (clock : Int) (statement : Resolved.Statement) :
    state.after (statement.atClock clock) = state.after statement := by
  have expressions : ∀ statement : Resolved.Statement,
      state.after (statement.expressionsAtClock clock) = state.after statement := by
    intro statement
    cases statement <;> rfl
  have filled : ∀ (cells : List Resolved.ClockCell) (statement : Resolved.Statement),
      state.after (statement.fillCells clock cells) = state.after statement := by
    intro cells statement
    cases statement <;> rfl
  cases statement with
  | clocked inner cells =>
    simp only [Resolved.Statement.atClock, expressions, filled]
    rfl
  | createTable | createIndex | addColumn | begin | commit | rollback | insert | update | upsert | delete
  | prepareError | query =>
    simp only [Resolved.Statement.atClock]
    exact expressions _

/-- For every clock assignment, script and state, the fold of {name}`ResolveState.after`
over the script under the clock assignment ({name}`scriptAtClock`) equals the fold over
the script. Proof sketch: induction on the script with the clock assignment shifted by one
position, rewriting each statement with {name}`ResolveState.after_atClock`. -/
theorem foldl_after_scriptAtClock (clock : Clock) (script : List Resolved.Statement) (state : ResolveState) :
    (scriptAtClock clock script).foldl ResolveState.after state = script.foldl ResolveState.after state := by
  induction script generalizing clock state with
  | nil => rfl
  | cons statement rest ih =>
    simp only [scriptAtClock, List.mapIdx_cons, List.foldl_cons, ResolveState.after_atClock]
    exact ih (fun position => clock (position + 1)) _

/-- Resolution and execution give the same catalog (ADR 0013, D1). For every context,
catalog, script, resolved statements and resulting catalog of a successful
{name}`resolve`, every database whose catalog is the starting catalog, and every clock
assignment: if {name}`runSqlAt` gives an outcome without an error (a success, or a pending
transaction without an error), its visible database's catalog is the resulting catalog of
resolution. An outcome with an error is not covered. Proof sketch: resolution's catalog is
the fold of {name}`ResolveState.after` ({name}`resolve_after`), the clock does not change
that fold, and execution follows it ({name}`runSqlFrom_agrees`). -/
theorem runSqlAt_catalog {context : ResolveContext} {catalog next : Catalog} {script : List Syntax.Statement}
    {resolved : List Resolved.Statement} {database : Database} (clock : Clock)
    (resolution : resolve context catalog script = .resolved resolved next) (start : database.catalog = catalog)
    (clean : (runSqlAt clock resolved database).error? = none) :
    (runSqlAt clock resolved database).database.catalog = next := by
  rw [resolve_after context catalog next script resolved resolution, ← foldl_after_scriptAtClock clock]
  exact runSqlFrom_agrees _ 0 { database } { catalog } ⟨start, rfl⟩ _ rfl clean

end Belay.Sqlite
