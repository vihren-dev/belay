import Belay.Sqlite.Model.Queries.Evaluation.CallSafety
import Belay.Sqlite.Model.Schema.Dispatch.SelectSubqueryRules
import Belay.Sqlite.Model.Schema.Dispatch.CorrelatedSubquerySource
import Belay.Sqlite.Model.Programs.Scripts.PlainDeleteRule

set_option doc.verso true

/-! A plain DELETE can run when it has its clock and counters and its filter is safe on the
stored rows and the empty row. These laws discharge the checks in the plain DELETE step rule. -/

namespace Belay.Sqlite.Model.PlainDeleteCoverage

/-- A DELETE without RETURNING passes the filter check if the filter is safe on the empty
row and on every stored row. -/
theorem ready_of_rows {ctx : Resolved.EvalContext} {table : Table} {filter : Option Resolved.Expr}
    (safe : ∀ row ∈ [] :: table.rows.map Row.values, filter.toList.any (·.mayFailOn ctx row) = false) :
    deleteJsonReady ctx table filter [] = true := by
  unfold deleteJsonReady Resolved.anyMayFail
  rw [List.any_eq_false.mpr (fun row mem => by rw [safe row mem]; decide)]
  rfl

/-- A statement without counter reads has no unknown counter. -/
theorem no_counters (s : Resolved.Statement) (c : Counters) (empty : s.counterReads = []) :
    c.firstUnknown s.counterReads = none := by rw [empty]; rfl

/-- A statement without clock reads gets the constant clock value zero. -/
theorem timed_without_read {s : Resolved.Statement} (h : s.readsClock = false) :
    statementClock clock index s = some 0 := by simp [statementClock, h]
/-- A clock-reading statement gets the supplied clock value at its statement index. -/
theorem timed_with_clock {s : Resolved.Statement} (h : s.readsClock = true)
    (known : clock = some f) : statementClock clock index s = some (f index) := by
  simp [statementClock, h, known]
/-- A statement that reads only changes() has its counter when the change count is known. -/
theorem changes_known {s : Resolved.Statement} {c : Counters}
    (reads : s.counterReads = [.changes]) (known : c.changes = some n) :
    c.firstUnknown s.counterReads = none := by simp [reads, Counters.firstUnknown, Counters.read, known]

open Resolved.CallSafety

/-- ABS can return a value when its argument differs from the smallest signed integer.
Proof sketch: inspect the storage class and exclude the overflowing integer. -/
theorem absSucceeds (v : Value) (safe : v ≠ .integer (-(2^63))) :
    Succeeds Resolved.ScalarFunction.abs.apply [v] := by
  cases v <;> try exact ⟨_, rfl⟩
  rename_i n
  have bound : n ≠ -9223372036854775808 := fun eq => safe (congrArg Value.integer eq)
  simp [Succeeds, Resolved.ScalarFunction.apply, bound]

/-- If {name}`Json.extract` returns a value for one text path, {name}`Json.apply` succeeds for
{name}`Resolved.JsonFunction.extract` on the value and the path with both JSON subtype flags false.
The evaluator reduces this call to the same extraction. -/
theorem extractSucceeds {value path} (ok : ∃ v, Json.extract value [.text path] = .ok v) :
    Succeeds (Json.apply .extract) [(value, false), (.text path, false)] := ok

/-- The inner SELECT of an IN test reads one column from one table. -/
private def projection (source column outer : Nat) (name : String) : Resolved.Query :=
  { Resolved.Query.simple [.first source] none [.scalar (.column column)] [name] with outer }

/-- An IN or NOT IN filter over a column and a single-column table scan has no fault on any
outer row when the source table exists. Proof sketch: the inner scan has no fault and its
unlimited window fixes the multiset of values. -/
theorem inProjection (db : Model.Database) (table : Table)
    (clock : Int) (counters : Counters) (parameters : List Value)
    (source column outer lhs : Nat) (name : String) (affinity : Option Affinity) (collation : Collation)
    (negated : Bool) (present : db.table source = some table) (row : List Value) :
    (some (Resolved.Expr.inQuery (.column lhs) 0 affinity collation negated)).toList.any
      (·.mayFailOn (Resolved.statementContext clock counters parameters db [projection source column outer name]) row) = false := by
  let q := projection source column outer name
  let ctx : Resolved.EvalContext := { Resolved.EvalContext.plain clock with parameters, counters }
  have run := Resolved.Query.subqueryRun_of_faultless ctx db row none (query := q) rfl rfl rfl
    (Resolved.Query.sourceAfter_first ctx db none q source _ row rfl present) rfl (by rfl)
    (fun r _ e member => by change e ∈ [Resolved.Expr.column column] at member; simp at member; subst e; rfl)
    (by simp [Resolved.Query.fails, q, projection, Resolved.Query.simple])
    (by simp [Resolved.Query.distinctCertain, q, projection, Resolved.Query.simple])
  change ((Resolved.Fault.none.join (if (q.subqueryRun ctx db row).rowsCertain then
    (q.subqueryRun ctx db row).fault else .may)) != .none || false) = false
  rw [run]; rfl

end Belay.Sqlite.Model.PlainDeleteCoverage
