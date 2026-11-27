import Belay

set_option doc.verso true
set_option sql.check false

namespace CompiledSelectCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open scoped Belay.Sqlite.LastOutput

/-- Two input rows give two copies of a constant projection. -/
private def items : Database := db! r"CREATE TABLE items (id INTEGER); INSERT INTO items VALUES (1), (2);"

/-- Project the supplied binding once per qualifying row. -/
private def byId (value : Value) : Script := sql r"SELECT ?1 FROM items WHERE id" value

/-- An extra conjunct accepts every qualifying row. -/
private def whereTrue (value : Value) : Script := sql r"SELECT ?1 FROM items WHERE id AND 1" value

/-- For every projection binding, adding a true conjunct leaves the certified scan unchanged.
Proof sketch: {lit}`sql_run` compares the two compiled outputs. -/
theorem equivalent (value : Value) : byId value ~ whereTrue value on items := by sql_run

/-- Reordering two different range tests and repeating one gives the same last output
on every database with this catalog. Proof sketch: compare the normalized SELECT plans. -/
theorem reordered_conjunction (lo hi : Value) :
    (sql r"SELECT id FROM items WHERE (id > ?1 AND id < ?2) AND id > ?1" lo hi) ~
    (sql r"SELECT id FROM items WHERE id < ?2 AND id > ?1" hi lo) on items := by sql_run

/-- Two equality tests with different parameter slots must both pass. The first slot alone
selects row one, the second selects row two, and their conjunction selects neither.
Proof sketch: compute the compiled SQL outputs with distinct bindings. -/
theorem distinct_bindings :
    let run := fun (s : Script) => ((s.compileLastOutput? items).map fun p => (p.val items Env.newConnection).1)
    let one := Value.integer 1
    let two := Value.integer 2
    run (sql r"SELECT id FROM items WHERE id = ?1" one) = some (some (.rows [[one]])) ∧
    run (sql r"SELECT id FROM items WHERE id = ?1" two) = some (some (.rows [[two]])) ∧
    run (sql r"SELECT id FROM items WHERE id = ?1 AND id = ?2" one two) = some (some (.rows [])) := by
  decide +kernel

/-- Check that the compiler preserves the bound operand and duplicate outputs on the
two-row fixture. A missing or ignored binding would project NULL instead of seven. -/
theorem bound_output :
    ((((byId (.integer 7)).compileLastOutput? items).get (by rfl)).val items Env.newConnection).1 =
      some (.rows [[.integer 7], [.integer 7]]) := by decide +kernel

/-- The first compiler case declines sequences and SELECTs with ordering. -/
theorem unsupported :
    (((byId .null) ++ (whereTrue .null)).compileLastOutput? items).isNone = true ∧
    ((sql r"SELECT id FROM items ORDER BY id").compileLastOutput? items).isNone = true := by
  exact ⟨rfl, rfl⟩

/-- Compile two closed WHERE expressions on an arbitrary input, then compare the plans.
Proof sketch: each compiled condition rejects every row. -/
theorem constant_filters :
    (sql r"SELECT 1 FROM items WHERE FALSE") ~ (sql r"SELECT 1 FROM items WHERE 1 = 2") on items := by
  sql_run

/-- The compiled plans coincide for any binding. Proof sketch: use reflexivity on the plans. -/
theorem identical (value : Value) : byId value ~ byId value on items := by sql_run

/-- Different closed filters leave a plan equality. The false premise lets the fixture
inspect that goal even though these scripts differ on a nonempty table.
Proof sketch: run the tactic, check the residual goal shape, then use the premise. -/
example (impossible : False) :
    (sql r"SELECT 1 FROM items WHERE 1 = 1") ~ (sql r"SELECT 1 FROM items WHERE 1 = 2") on items := by
  sql_run
  change _ = _
  exact impossible.elim

/-- error: sql_run: unsupported query on the left of ~ -/
#guard_msgs in
example : (sql r"SELECT id FROM items ORDER BY id") ~ byId .null on items := by sql_run

/-- error: sql_run: unsupported query on the right of ~ -/
#guard_msgs in
example : byId .null ~ (sql r"SELECT id FROM items ORDER BY id") on items := by sql_run

/-- A sum of two columns compiles to SQL addition on arbitrary input values.
Proof sketch: reduce the row function on a row containing the two operands. -/
theorem column_sum (args : List Value) (x y : Value) :
    (CompiledExpr.compile args (.arithmetic .add (.column 0) (.column 1))).run [x, y] =
      (ArithmeticOperator.add.apply x y, .none) := by rfl

/-- An overflowing constant call carries its fault even when evaluated without a row.
Proof sketch: compute the fault of the compiled absolute value. -/
theorem constant_fault :
    ((CompiledExpr.compile [] (.scalar .abs (.cons (.literal (.integer (-9223372036854775808))) .nil))).run []).2 =
      .must := by decide +kernel

/-- Run the compiled SQL projection on numeric and NULL operands.
Proof sketch: compare the resulting bag with the two expected rows. -/
theorem sum_output :
    let input := db! r"CREATE TABLE t(a, b); INSERT INTO t VALUES (2, 3), (NULL, 7);"
    let script := sql r"SELECT a + b FROM t"
    (((script.compileLastOutput? input).get (by rfl)).val input Env.newConnection).1 =
      (LastOutputPlan.rowBag [[.integer 5], [.null]]).1 := by decide +kernel

#print axioms reordered_conjunction
#print axioms distinct_bindings
#print axioms equivalent
#print axioms bound_output
#print axioms unsupported
#print axioms identical
#print axioms constant_filters
#print axioms column_sum
#print axioms constant_fault
#print axioms sum_output

end CompiledSelectCases
