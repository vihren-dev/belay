import Belay

set_option doc.verso true
set_option sql.check false

/-! Acceptance contrasts of B11 under ADR 0027: a preparation error in the body of a SELECT, and
preparation errors in nested queries. {lit}`SelectOutcomeCases` holds the main case, a missing
table. A body error holds for every database and environment, through the body resolution law
({lit}`resolveStatement_select_body_prepareError`) and the prepare-error rule
({lit}`Run.query_prepareError`). Each nested form keeps the error of its nested query, with the code
1 of a resolution error, on a concrete database. -/

namespace SelectPrepareErrorCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- A query without {lit}`FROM` of a column {lit}`missing`, which no scope has. -/
def unknownColumn : Script := sql r"SELECT missing"

/-- The query of the unknown column has one statement. -/
theorem unknownColumn_one : unknownColumn.statements.length = 1 := rfl

/-- B11 with an error in the body: for every database and environment, the query of the unknown
column

* returns no result with any property, also not an empty one, and
* returns an error with a property exactly when the property holds of code 1, the code of the
  resolution error {lit}`no such column` ({name}`ExprError.noSuchColumn`).

Proof sketch: without {lit}`FROM` the sources and the star check are empty, and the body reports
the error ({name}`resolveStatement_select_body_prepareError`); then {name}`Run.query_prepareError`. -/
theorem unknown_column_error (db : Database) (env : Env) :
    (∀ property, ¬ (db.run (query unknownColumn unknownColumn_one) env).returnsResult property) ∧
      ∀ code : Nat → Prop, (db.run (query unknownColumn unknownColumn_one) env).returnsError code ↔ code 1 := by
  let body : Syntax.Subquery := ⟨[.expression (.identifier (name! "missing") .none) none "missing"],
    none, [], none, [], [], none, none, none, none, false, none, none⟩
  have resolved := resolveStatement_select_body_prepareError runContext (db.raw.connection env.counters).resolveState
    body [] [] (.noSuchColumn (name! "missing")) rfl rfl rfl (resolveSources_none _) rfl (by decide +kernel)
  exact ⟨fun property => (Run.query_prepareError (script := unknownColumn) rfl unknownColumn_one db env resolved
      property (fun _ => True)).1,
    fun code => (Run.query_prepareError (script := unknownColumn) rfl unknownColumn_one db env resolved
      (fun _ => True) code).2⟩

/-- One table {lit}`t` whose only column is {lit}`x`, for the nested cases. -/
def sample : Database := db! r"CREATE TABLE t (x INTEGER); INSERT INTO t VALUES (1);"

/-- A missing table in a table query gives the error code 1. -/
example : (sample.run (sql r"SELECT 1 FROM missing WHERE x = 1")).returnsError (· = 1) := by decide +kernel

/-- A missing filter column gives the error code 1, although the table exists. -/
example : (sample.run (sql r"SELECT 1 FROM t WHERE missing = 1")).returnsError (· = 1) := by decide +kernel

/-- {lit}`EXISTS` keeps the error of a missing nested table. -/
example : (sample.run (sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM missing)")).returnsError (· = 1) := by
  decide +kernel

/-- {lit}`NOT EXISTS` does not turn a missing nested column into truth. -/
example : (sample.run (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM t WHERE missing = 1)")).returnsError
    (· = 1) := by
  decide +kernel

/-- {lit}`IN` keeps the error of a missing result column in its nested query. -/
example : (sample.run (sql r"SELECT 1 WHERE 1 IN (SELECT missing FROM t)")).returnsError (· = 1) := by
  decide +kernel

/-- A nested {lit}`count(*)` keeps the error of a missing table. -/
example : (sample.run (sql r"SELECT 1 WHERE (SELECT count(*) FROM missing) <= 1")).returnsError (· = 1) := by
  decide +kernel

/-- A duplicate-key check keeps the error of a missing grouping column. -/
example : (sample.run (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM t GROUP BY missing HAVING count(*) > 1)")).returnsError
    (· = 1) := by
  decide +kernel

/-- {lit}`sum` keeps the error of a missing operand column. -/
example : (sample.run (sql r"SELECT sum(missing) FROM t")).returnsError (· = 1) := by decide +kernel

/-- The result columns of a pragma source are resolved too: an unknown name gives the error code 1. -/
example : (sample.run (sql r"SELECT 1 FROM pragma_table_info('t') WHERE missing = 1")).returnsError (· = 1) := by
  decide +kernel

/-- Contrast: with the known column {lit}`x` the same query returns no error. -/
example : ¬ (sample.run (sql r"SELECT 1 FROM t WHERE x = 1")).returnsError fun _ => True := by decide +kernel

end SelectPrepareErrorCases

#print axioms SelectPrepareErrorCases.unknown_column_error
