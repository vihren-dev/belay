import SelectSumCases

set_option doc.verso true
set_option sql.check false

/-! Instances and integer laws of the {lit}`sum` claims of A09 (ADR 0027): the claims of
{name}`SelectSumCases.sumCents_claims` on five ledgers, where {lit}`decide +kernel` checks the
premise, and the free-input {lit}`sum` laws of the simp set {lit}`sql_simp`, which turn the claim
for a column of integers into integer prefix sums. A prefix sum outside the 64-bit range fails the
run even when a later value brings the sum back into the range. -/

namespace SelectSumCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- A ledger with two rows of 4611686018427387904 (2 to the power 62): their sum, 2 to the power 63,
is more than the largest 64-bit integer. -/
def bigLedger : Database := db! r"
  CREATE TABLE ledger (id INTEGER PRIMARY KEY, cents INTEGER);
  INSERT INTO ledger (id, cents) VALUES (1, 4611686018427387904), (2, 4611686018427387904);"

/-- A ledger with two small rows. -/
def smallLedger : Database := db! r"
  CREATE TABLE ledger (id INTEGER PRIMARY KEY, cents INTEGER);
  INSERT INTO ledger (id, cents) VALUES (1, 10), (2, 20);"

/-- A ledger without a row. -/
def emptyLedger : Database := db! r"
  CREATE TABLE ledger (id INTEGER PRIMARY KEY, cents INTEGER);"

/-- A ledger whose largest integer and then 1 leave the range, and whose last row, -1, brings the
final sum back into it. -/
def cancelLedger : Database := db! r"
  CREATE TABLE ledger (id INTEGER PRIMARY KEY, cents INTEGER);
  INSERT INTO ledger (id, cents) VALUES (1, 9223372036854775807), (2, 1), (3, -1);"

/-- A ledger whose column {lit}`cents` is TEXT, with eleven rows {lit}`'0999999999999999999'`:
{lit}`sum` reads each text as the integer 999999999999999999, and the sum of eleven of them is more
than the largest 64-bit integer. -/
def textLedger : Database := db! r"
  CREATE TABLE ledger (id INTEGER PRIMARY KEY, cents TEXT);
  INSERT INTO ledger (id, cents) VALUES (1, '0999999999999999999'), (2, '0999999999999999999'),
    (3, '0999999999999999999'), (4, '0999999999999999999'), (5, '0999999999999999999'), (6, '0999999999999999999'),
    (7, '0999999999999999999'), (8, '0999999999999999999'), (9, '0999999999999999999'), (10, '0999999999999999999'),
    (11, '0999999999999999999');"

/-- The catalog table {lit}`ledger` of a database that has one. -/
def ledgerOf (db : Database) (present : (db.raw.catalog.findTable (name! "ledger")).isSome := by decide +kernel) :
    CatalogTable :=
  ((db.raw.catalog.findTable (name! "ledger")).get present).2

-- Two rows of 2 to the power 62: the run fails with the code of `integer overflow`.
example : Fails sumCents bigLedger ∧ ¬ Holds sumCents bigLedger ∧ ¬ Belay.Sqlite.Empty sumCents bigLedger := by
  obtain ⟨fails, holds, empty⟩ := sumCents_claims bigLedger (position := 0) (index := 1) (table := ledgerOf bigLedger)
    (by decide +kernel) (by decide +kernel)
  exact ⟨fails.mpr (by decide +kernel), fun held => absurd (holds.mp held) (by decide +kernel), empty⟩
example : (bigLedger.run (query sumCents sumCents_one)).returnsError (· = ExecutionError.integerOverflow.primaryCode) :=
  ((sumCents_overflow bigLedger Env.default (position := 0) (index := 1) (table := ledgerOf bigLedger)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ => True) _).2).mpr rfl

-- Two small rows: the run returns the row of 30, and it does not fail.
example : (smallLedger.run (query sumCents sumCents_one)).returnsResult (· = [[.integer 30]]) ∧
    ¬ Fails sumCents smallLedger := by
  obtain ⟨fails, -, -⟩ := sumCents_claims smallLedger (position := 0) (index := 1) (table := ledgerOf smallLedger)
    (by decide +kernel) (by decide +kernel)
  exact ⟨(sumCents_results smallLedger Env.default (position := 0) (index := 1) (table := ledgerOf smallLedger)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _).mpr (by decide +kernel),
    fun failed => absurd (fails.mp failed) (by decide +kernel)⟩

-- A ledger without a row: the run returns the row of NULL, not an empty result.
example : (emptyLedger.run (query sumCents sumCents_one)).returnsResult (· = [[.null]]) ∧
    ¬ Belay.Sqlite.Empty sumCents emptyLedger :=
  ⟨(sumCents_results emptyLedger Env.default (position := 0) (index := 1) (table := ledgerOf emptyLedger)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _).mpr (by decide +kernel),
    (sumCents_claims emptyLedger (position := 0) (index := 1) (table := ledgerOf emptyLedger)
      (by decide +kernel) (by decide +kernel)).2.2⟩

-- A prefix sum outside the range fails the run, although the final sum, the largest integer, fits.
example : Fails sumCents cancelLedger :=
  (sumCents_claims cancelLedger (position := 0) (index := 1) (table := ledgerOf cancelLedger)
    (by decide +kernel) (by decide +kernel)).1.mpr (by decide +kernel)

-- Eleven texts that read as 999999999999999999: the run fails.
example : Fails sumCents textLedger :=
  (sumCents_claims textLedger (position := 0) (index := 1) (table := ledgerOf textLedger)
    (by decide +kernel) (by decide +kernel)).1.mpr (by decide +kernel)

/-- For every group and context, {lit}`sql_simp` turns {lit}`count(*)` into the number of rows
and proves that it does not fail. -/
example (context : Resolved.EvalContext) (rows : List (List Value)) :
    Resolved.Aggregate.countRows.eval context rows = .integer rows.length ∧
      Resolved.Aggregate.countRows.fails context rows = false := by
  simp [sql_simp]

/-- The same laws are available to {lit}`grind`, without unfolding the aggregate evaluator. -/
example (context : Resolved.EvalContext) (rows : List (List Value)) :
    Resolved.Aggregate.countRows.eval context rows = .integer rows.length ∧
      Resolved.Aggregate.countRows.fails context rows = false := by
  grind

/-- For every context, rows and operand whose value on each row is NULL or an integer,
{lit}`sum` of the operand fails exactly when some prefix of the integer values has a sum outside the
64-bit range. Proof sketch: {lit}`sql_simp` applies the sum-failure equation and the
integer-prefix law. -/
theorem integer_sum_failure (context : Resolved.EvalContext) (rows : List (List Value))
    (operand : Resolved.Expr)
    (cells : ∀ value ∈ rows.map (operand.eval context), value = .null ∨ ∃ number, value = .integer number) :
    (Resolved.Aggregate.sum operand).fails context rows = true ↔
      ∃ k, fitsInt64Range ((integerCells (rows.map (operand.eval context))).take k).sum = false := by
  simp (disch := assumption) only [sql_simp]

/-- For every context, rows and operand whose value on each row is NULL or an integer, and every
prefix of whose integer values has a sum in the 64-bit range, {lit}`sum` of the operand is NULL
when there is no integer value and otherwise the exact sum of the integer values. Proof sketch:
{lit}`sql_simp` applies the aggregate-value equation and the exact-fold law. -/
theorem integer_sum_value (context : Resolved.EvalContext) (rows : List (List Value))
    (operand : Resolved.Expr)
    (cells : ∀ value ∈ rows.map (operand.eval context), value = .null ∨ ∃ number, value = .integer number)
    (fits : ∀ k, fitsInt64Range ((integerCells (rows.map (operand.eval context))).take k).sum = true) :
    (Resolved.Aggregate.sum operand).eval context rows =
      if integerCells (rows.map (operand.eval context)) = [] then .null
      else .integer (integerCells (rows.map (operand.eval context))).sum := by
  simp (disch := assumption) only [sql_simp, Option.getD_some]

/-- A09 for a ledger of integers: for every database and environment as in
{name}`sumCents_results` whose cents on the scan are NULL or integers, and every prefix of whose
integer cents has a sum in the 64-bit range, the run of {name}`sumCents` returns the row of NULL
when there is no integer cent, and otherwise the row of their exact sum. Proof sketch:
{name}`integer_sum_failure` excludes the overflow, {name}`sumCents_results` gives the one row, and
{name}`integer_sum_value` its value. -/
theorem integer_cents (db : Database) (env : Env) {position index : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "ledger") = some (position, table))
    (column : columnPosition table.columns (name! "cents") = some index)
    (cells : ∀ value ∈ (scanOf db position table).map ((Resolved.Expr.column index).eval (Resolved.EvalContext.bound [])),
      value = .null ∨ ∃ number, value = .integer number)
    (fits : ∀ k, fitsInt64Range ((integerCells ((scanOf db position table).map
      ((Resolved.Expr.column index).eval (Resolved.EvalContext.bound [])))).take k).sum = true) :
    (db.run (query sumCents sumCents_one) env).returnsResult (· = [[
      if integerCells ((scanOf db position table).map ((Resolved.Expr.column index).eval (Resolved.EvalContext.bound []))) = []
      then .null
      else .integer (integerCells ((scanOf db position table).map
        ((Resolved.Expr.column index).eval (Resolved.EvalContext.bound [])))).sum]]) := by
  have safe : (centsSum index).fails (Resolved.EvalContext.bound []) (scanOf db position table) = false :=
    Bool.eq_false_iff.mpr fun failed => by
      obtain ⟨k, outside⟩ := (integer_sum_failure _ _ _ cells).mp failed
      simp [fits k] at outside
  exact (sumCents_results db env found column safe _).mpr (by rw [integer_sum_value _ _ _ cells fits])

/-- {lit}`sum` skips NULL and keeps a fitting integer sum exact. -/
example : (sumOf [.null, .integer 10, .integer (-3)]).sumValue = some (.integer 7) := by decide +kernel

/-- With no integer input {lit}`sum` returns NULL. -/
example : (sumOf [.null, .null]).sumValue = some .null := by decide +kernel

/-- A fitting sum has no overflowing prefix, so the failure equivalence has a negative instance. -/
example : ¬ ∃ k, fitsInt64Range ((integerCells [.null, .integer 10, .integer (-3)]).take k).sum = false := by
  intro outside
  have failed := (sumOf_fails_iff [.null, .integer 10, .integer (-3)] (by simp)).2 outside
  have safe : (sumOf [.null, .integer 10, .integer (-3)]).sumValue.isNone = false := by decide +kernel
  simp [safe] at failed

#print axioms integer_sum_failure
#print axioms integer_sum_value
#print axioms integer_cents

end SelectSumCases
