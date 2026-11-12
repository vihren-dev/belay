import Belay

set_option doc.verso true
set_option sql.check false

/-! Function faults of a {lit}`SELECT` without {lit}`FROM`, through the phase rules of ADR 0027
(B01, B05). A call of {lit}`abs` is quiet ({lit}`Resolved.Statement.Quiet`) but not calm, because
{lit}`abs` can fail. Over every database and environment: {lit}`SELECT abs(1)` returns the one row 1
through the readiness of its phases ({lit}`Connection.SelectReady.of_phases`);
{lit}`SELECT abs(-9223372036854775808)` returns the error of a failing function and no result
through the failure rule ({lit}`Run.send_mustFail`); and with {lit}`WHERE 0` the same call is
never evaluated, so the query returns no row. -/

namespace SelectFunctionFaultCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The call {lit}`abs(n)` of a known integer {lit}`n`. -/
def absCall (argument : Int) : Resolved.Expr := .scalar .abs (.cons (.literal (.integer argument)) .nil)

/-- The query {lit}`SELECT abs(n) [WHERE c]` without a source, with the name of its column. -/
def absQuery (argument : Int) (condition : Option Resolved.Expr) (name : String) : Resolved.Query :=
  Resolved.Query.simple [] condition [.scalar (absCall argument)] [name]

/-- For every argument, name and condition whose parts are quiet, the statement of
{name}`absQuery` is quiet. -/
theorem absQuery_quiet (argument : Int) (condition : Option Resolved.Expr) (name : String)
    (quiet : ∀ part ∈ condition.toList, part.Quiet) :
    (Resolved.Statement.query (absQuery argument condition name) []).Quiet :=
  Resolved.Statement.Quiet.selectNoFrom _ _ _ quiet ⟨rfl, fun _ => rfl⟩

/-- For every database, environment, argument, condition and name of a quiet statement of
{name}`absQuery`, the step runs the statement at the clock value 0, and the query evaluates in the
context of no values ({name}`Resolved.EvalContext.bound`). -/
theorem abs_context (db : Database) (env : Env) {argument : Int} {condition : Option Resolved.Expr}
    {name : String} (quiet : (Resolved.Statement.query (absQuery argument condition name) []).Quiet) :
    statementClock env.clock 0 (.query (absQuery argument condition name) []) = some 0 ∧
      (db.raw.connection env.counters).queryContextAt 0 [] (absQuery argument condition name) [] =
        Resolved.EvalContext.bound [] :=
  ⟨by simp [statementClock, quiet.readsClock], Connection.queryContext_of_quiet _ [] _ quiet⟩

/-- B05 with a call that can fail: for every database and environment, {lit}`SELECT abs(1)`
returns the one row 1. Proof sketch: {name}`Run.send_returnsResult_select` with
{name}`Connection.SelectReady.of_phases`; the statement is not calm, but its call has a known
argument, so each phase obligation is a closed computation in the context of no values. -/
theorem abs_one_returns (db : Database) (env : Env) :
    (db.run (sql r"SELECT abs(1)") env).returnsResult (· = [[.integer 1]]) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (sql r"SELECT abs(1)").statements[0].1 =
      .ok (.query (absQuery 1 none "abs(1)") [], (db.raw.connection env.counters).resolveState) :=
    resolveStatement_selectNoFrom_columns runContext _ (.call "abs" [.numeric "1"]) "abs(1)" "abs(1)" none
      (absCall 1) none none (by decide +kernel) (by decide +kernel) (by decide +kernel) (FilterResolves.of_none _ _ _ _)
  have quiet := absQuery_quiet 1 none "abs(1)" (by simp)
  obtain ⟨clocked, context⟩ := abs_context db env quiet
  rw [Run.send_returnsResult_select (script := sql r"SELECT abs(1)") rfl db env resolved clocked
    (Connection.SelectReady.of_phases rfl (quiet.firstUnknown _) (Resolved.Query.source_none _ _ _ rfl) rfl (by simp)
      (Resolved.Query.bindWindow_literal _ _ rfl rfl) (by rw [context]; decide +kernel) (by rw [context]; decide +kernel)
      (by rw [context]; decide +kernel) (by rw [context]; decide +kernel)), context]
  decide +kernel

/-- B01 with a function error: for every database, environment, property {lit}`Q` of a result
and property {lit}`E` of a result code, {lit}`SELECT abs(-9223372036854775808)` returns no result
with {lit}`Q`, and returns an error with {lit}`E` exactly when {lit}`E` holds of the primary code of
a failing function. Proof sketch: {name}`Run.send_mustFail`; the call certainly fails on the one
row of a query without a source. -/
theorem abs_least_fails (db : Database) (env : Env) (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run (sql r"SELECT abs(-9223372036854775808)") env).returnsResult property ∧
      ((db.run (sql r"SELECT abs(-9223372036854775808)") env).returnsError code ↔
        code ExecutionError.functionError.primaryCode) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (sql r"SELECT abs(-9223372036854775808)").statements[0].1 =
      .ok (.query (absQuery (-9223372036854775808) none "abs(-9223372036854775808)") [],
        (db.raw.connection env.counters).resolveState) :=
    resolveStatement_selectNoFrom_columns runContext _ (.call "abs" [.negate (.numeric "9223372036854775808")])
      "abs(-9223372036854775808)" "abs(-9223372036854775808)" none (absCall (-9223372036854775808)) none none
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (FilterResolves.of_none _ _ _ _)
  have quiet := absQuery_quiet (-9223372036854775808) none "abs(-9223372036854775808)" (by simp)
  obtain ⟨clocked, context⟩ := abs_context db env quiet
  exact Run.send_mustFail rfl db env resolved rfl clocked (quiet.firstUnknown _) (Resolved.Query.source_none _ _ _ rfl)
    rfl (by simp) (Resolved.Query.bindWindow_literal _ _ rfl rfl) (by rw [context]; decide +kernel)
    (by rw [context]; decide +kernel) property code

/-- B05 with a false filter: for every database and environment,
{lit}`SELECT abs(-9223372036854775808) WHERE 0` returns no row: the filter removes the one row of
the query before the call is evaluated. Proof sketch: as {name}`abs_one_returns`; the call that can
fail is not evaluated, so no phase obligation reads its fault. -/
theorem abs_least_skipped (db : Database) (env : Env) :
    (db.run (sql r"SELECT abs(-9223372036854775808) WHERE 0") env).returnsResult (· = []) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (sql r"SELECT abs(-9223372036854775808) WHERE 0").statements[0].1 =
      .ok (.query (absQuery (-9223372036854775808) (some (.literal (.integer 0))) "abs(-9223372036854775808)") [],
        (db.raw.connection env.counters).resolveState) :=
    resolveStatement_selectNoFrom_columns runContext _ (.call "abs" [.negate (.numeric "9223372036854775808")])
      "abs(-9223372036854775808)" "abs(-9223372036854775808)" (some (.numeric "0")) (absCall (-9223372036854775808))
      none (some (.literal (.integer 0))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (FilterResolves.of_term (result := (.literal (.integer 0), none)) (by decide +kernel) (by decide +kernel))
  have quiet := absQuery_quiet (-9223372036854775808) (some (.literal (.integer 0))) "abs(-9223372036854775808)"
    (by simpa using (Resolved.Expr.calm_literal _).quiet)
  obtain ⟨clocked, context⟩ := abs_context db env quiet
  rw [Run.send_returnsResult_select
    (script := sql r"SELECT abs(-9223372036854775808) WHERE 0") rfl db env resolved clocked
    (Connection.SelectReady.of_phases rfl (quiet.firstUnknown _) (Resolved.Query.source_none _ _ _ rfl) rfl (by simp)
      (Resolved.Query.bindWindow_literal _ _ rfl rfl) (by rw [context]; decide +kernel) (by rw [context]; decide +kernel)
      (by rw [context]; decide +kernel) (by rw [context]; decide +kernel)), context]
  decide +kernel

/-- A database with one empty table, on which the instances check each claim against the run. -/
def blank : Database := db! r"CREATE TABLE t (x INTEGER);"

-- The claims on blank, and their contrasts. Native SQLite 3.51.0 gives the row 1, no row, and the
-- error "integer overflow" with the result code 1 (SQLITE_ERROR) for the call that fails.
example : Holds (sql r"SELECT abs(1)") blank ∧ ¬ Empty (sql r"SELECT abs(1)") blank ∧
    ¬ Fails (sql r"SELECT abs(1)") blank := by decide +kernel
example : Fails (sql r"SELECT abs(-9223372036854775808)") blank ∧
    ¬ Holds (sql r"SELECT abs(-9223372036854775808)") blank ∧
    ¬ Empty (sql r"SELECT abs(-9223372036854775808)") blank ∧ ExecutionError.functionError.primaryCode = 1 := by
  decide +kernel
example : Empty (sql r"SELECT abs(-9223372036854775808) WHERE 0") blank ∧
    ¬ Holds (sql r"SELECT abs(-9223372036854775808) WHERE 0") blank ∧
    ¬ Fails (sql r"SELECT abs(-9223372036854775808) WHERE 0") blank := by decide +kernel
-- The general claims give the same sides on blank.
example : Fails (sql r"SELECT abs(-9223372036854775808)") blank :=
  ((abs_least_fails blank Env.default (fun _ => True) (fun _ => True)).2).mpr trivial
example : Empty (sql r"SELECT abs(-9223372036854775808) WHERE 0") blank := abs_least_skipped blank Env.default
example : Holds (sql r"SELECT abs(1)") blank :=
  (abs_one_returns blank Env.default).mono fun _ same => by simp [same]

#print axioms abs_one_returns
#print axioms abs_least_fails
#print axioms abs_least_skipped

end SelectFunctionFaultCases
