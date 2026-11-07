import Belay

/-! A fixture of `tests/surface_claims_test.py`: a query whose `WHERE` may fail has no modeled output,
through the rule of a SELECT that is not ready (`Run.send_unready`, ADR 0027). `abs` fails on the
smallest 64-bit integer, so `SELECT 1 FROM t WHERE abs(x) = 1` on a table with the rows
`-9223372036854775808` and `1` returns a row and then fails in SQLite (measured 2026-10-24); the model
gives the output `Output.unmodeled`, and none of `Holds`, `Empty` and `Fails` holds. The same query on
a table without that row holds. -/

set_option doc.verso true

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- A table {lit}`t` with the smallest 64-bit integer and the integer 1. -/
def numbers : Database := db! r"
  CREATE TABLE t (x INTEGER);
  INSERT INTO t (x) VALUES (-9223372036854775808), (1);"

/-- A table {lit}`t` without that integer, where {lit}`abs(x) = 1` is true for the row 1. -/
def smaller : Database := db! r"
  CREATE TABLE t (x INTEGER);
  INSERT INTO t (x) VALUES (-5), (1);"

/-- The query {lit}`SELECT 1 FROM t WHERE abs(x) = 1`. -/
def absScript : Script := sql r"SELECT 1 FROM t WHERE abs(x) = 1"

example : ¬ Holds absScript numbers := by decide +kernel
example : ¬ Empty absScript numbers := by decide +kernel
example : ¬ Fails absScript numbers := by decide +kernel
example : Holds absScript smaller := by decide +kernel

/-- The condition {lit}`abs(x) = 1` as it resolves on a table whose first column is {lit}`x`. -/
def absCondition : Resolved.Expr :=
  .compare .eq none (.scalar .abs (.cons (.column 0) .nil)) (.literal (.integer 1)) .binary

/-- The condition {lit}`abs(x) = 1` reads no clock and no counter. -/
theorem absCondition_quiet : ∀ expression ∈ (some absCondition).toList, expression.Quiet := by
  intro expression member
  simp only [Option.toList, List.mem_singleton] at member
  subst member
  exact ⟨by decide +kernel, fun kind => by cases kind <;> decide +kernel⟩

/-- The syntax of {lit}`abs(x) = 1`. -/
def absFilter : Syntax.Expr := .compare .eq (.call "abs" [.identifier (name! "x") .none]) (.numeric "1")

/-- For every database whose table {lit}`t` is at a position, where {lit}`abs(x) = 1` resolves to
{name}`absCondition`, and every environment, property {lit}`Q` of a result and property {lit}`E` of a
result code: when {name}`absCondition` may fail on a source row of the table, the run of
{name}`absScript` returns neither a result with {lit}`Q` nor an error with {lit}`E`. Proof sketch:
{name}`Run.send_unready`; the run of the query possibly fails ({name}`Resolved.Query.run_single`),
because the filter may fail on the row and a query with a source does not certainly fail. -/
theorem abs_where_unmodeled (db : Database) (env : Env) (position : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "t") = some (position, table))
    (resolves : FilterResolves runContext.profile.dqsDml
      (tableScope db.raw.catalog { table := name! "t", alias := none } position table) [] (some absFilter)
      (some absCondition) { later := [] })
    {row : List Value} (member : row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] })
    (fails : absCondition.mayFailOn (Resolved.EvalContext.bound []) row = true)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run absScript env).returnsResult property ∧ ¬ (db.run absScript env).returnsError code := by
  have quiet := Resolved.Statement.Quiet.selectOne position _ absCondition_quiet
  have resolved := resolveStatement_select_one_from runContext (db.raw.connection env.counters).resolveState
    { table := name! "t", alias := none } _ position table _ rfl rfl rfl found resolves
  have context : (db.raw.connection env.counters).queryContextAt 0 []
      (Resolved.Query.simple [.first position] (some absCondition) [.scalar (.literal (.integer 1))] ["1"]) [] =
      Resolved.EvalContext.bound [] :=
    Connection.queryContext_of_quiet _ [] _ quiet
  refine Run.send_unready rfl db env resolved (value := 0) (by simp [statementClock, quiet.readsClock])
    (quiet.firstUnknown _)
    (Resolved.Query.source_first _ _ _ position _ rfl (Database.table_of_findTable db.raw _ position table found))
    (.inr (.inr ?_)) property code
  rw [context, Resolved.Query.run_single _ _ _ rfl (Resolved.Query.bindWindow_literal _ _ rfl rfl)]
  have mayFail :
      (Resolved.Query.simple [.first position] (some absCondition) [.scalar (.literal (.integer 1))] ["1"]).mayFail
        (Resolved.EvalContext.bound []) (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }) =
        true := by
    unfold Resolved.Query.mayFail Resolved.anyMayFail
    simp only [Bool.or_eq_true]
    exact .inr (.inl (List.any_eq_true.mpr ⟨row, List.mem_cons_of_mem _ member,
      List.any_eq_true.mpr ⟨absCondition, by simp [Resolved.Query.simple], fails⟩⟩))
  have mustFail :
      (Resolved.Query.simple [.first position] (some absCondition) [.scalar (.literal (.integer 1))] ["1"]).mustFail
        (Resolved.EvalContext.bound []) (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }) =
        false := by
    simp [Resolved.Query.mustFail, Resolved.Query.simple]
  simp only [mustFail, mayFail, Bool.false_eq_true, ite_false, Bool.true_or, ite_true]

/-- The catalog position and the table of {lit}`t` in {name}`numbers`. -/
def numbersTable : Nat × CatalogTable := (numbers.raw.catalog.findTable (name! "t")).get (by decide +kernel)

/-- On {name}`numbers`, {name}`abs_where_unmodeled` gives the three facts from the row of the
smallest integer, on which {lit}`abs` may fail. -/
example : ¬ Holds absScript numbers ∧ ¬ Empty absScript numbers ∧ ¬ Fails absScript numbers := by
  have unmodeled := abs_where_unmodeled numbers Env.default numbersTable.1 numbersTable.2 (by decide +kernel)
    (FilterResolves.of_term (result := (absCondition, none)) (by decide +kernel) (by decide +kernel))
    (row := [.integer (-9223372036854775808)]) (by decide +kernel) (by decide +kernel)
  exact ⟨(unmodeled (· ≠ []) fun _ => True).1, (unmodeled (· = []) fun _ => True).1,
    (unmodeled (· ≠ []) fun _ => True).2⟩

/-- The query {lit}`SELECT 1 WHERE EXISTS (SELECT 1 FROM t WHERE abs(x) = 1)`. SQLite may evaluate a
subquery for rows that the model does not reach, so the model does not describe a call that can fail in
a subquery: for every table, the output is {name}`Output.unmodeled`, also for {name}`smaller`, where
{lit}`abs` cannot fail. -/
def absExists : Script := sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM t WHERE abs(x) = 1)"

example : ¬ Holds absExists numbers ∧ ¬ Empty absExists numbers ∧ ¬ Fails absExists numbers := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

example : ¬ Holds absExists smaller := by decide +kernel

/-- For every database whose table {lit}`t` is at a position, where {lit}`abs(x) = 1` resolves to
{name}`absCondition` in the subquery, and every environment, property {lit}`Q` of a result and property
{lit}`E` of a result code: the run of {name}`absExists` returns neither a result with {lit}`Q` nor an
error with {lit}`E`, whatever the rows of the table. Proof sketch: {name}`Run.send_unready`; the
call of {lit}`abs` makes the subquery not plain ({name}`Resolved.subqueriesPlain`). -/
theorem abs_exists_unmodeled (db : Database) (env : Env) (position : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "t") = some (position, table))
    (resolves : FilterResolves runContext.profile.dqsDml
      (tableScope db.raw.catalog { table := name! "t", alias := none } position table) [] (some absFilter)
      (some absCondition) { current := some 0 })
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run absExists env).returnsResult property ∧ ¬ (db.run absExists env).returnsError code := by
  have quiet := Resolved.Statement.Quiet.selectOne_subquery position (.exists 0) (some absCondition)
    (.literal (.integer 1)) ["1"] (Resolved.Expr.calm_exists 0).quiet absCondition_quiet
    (Resolved.Expr.calm_literal _).quiet
  have resolved := resolveStatement_selectOne_exists runContext (db.raw.connection env.counters).resolveState
    { table := name! "t", alias := none } _ position table _ rfl rfl rfl found resolves
  exact Run.send_unready rfl db env resolved (value := 0) (by simp [statementClock, quiet.readsClock])
    (quiet.firstUnknown _)
    (Resolved.Query.source_none _ _ _ rfl)
    (.inl (by simp [Resolved.subqueriesPlain, Resolved.Query.nestedSubqueries, Resolved.Query.selectOneWhere,
      Resolved.Query.simple, Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.QuerySource.first,
      Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands, absCondition,
      Resolved.Expr.any, Resolved.Expr.isFallibleCall, Resolved.ScalarFunction.canFail]))
    property code

/-- The catalog position and the table of {lit}`t` in {name}`smaller`. -/
def smallerTable : Nat × CatalogTable := (smaller.raw.catalog.findTable (name! "t")).get (by decide +kernel)

/-- On {name}`numbers` and on {name}`smaller`, {name}`abs_exists_unmodeled` gives the three facts, also
where {lit}`abs` cannot fail. -/
example : ¬ Holds absExists numbers ∧ ¬ Empty absExists numbers ∧ ¬ Fails absExists numbers ∧
    ¬ Holds absExists smaller := by
  have onNumbers := abs_exists_unmodeled numbers Env.default numbersTable.1 numbersTable.2 (by decide +kernel)
    (FilterResolves.of_term (result := (absCondition, none)) (by decide +kernel) (by decide +kernel))
  have onSmaller := abs_exists_unmodeled smaller Env.default smallerTable.1 smallerTable.2 (by decide +kernel)
    (FilterResolves.of_term (result := (absCondition, none)) (by decide +kernel) (by decide +kernel))
  exact ⟨(onNumbers (· ≠ []) fun _ => True).1, (onNumbers (· = []) fun _ => True).1,
    (onNumbers (· ≠ []) fun _ => True).2, (onSmaller (· ≠ []) fun _ => True).1⟩

#print axioms abs_where_unmodeled
#print axioms abs_exists_unmodeled
