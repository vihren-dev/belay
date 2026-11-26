import Lean.LabelAttribute
import Belay.Sqlite.Model.Schema.Dispatch.SelectSubqueryRules
import Belay.Sqlite.Model.Schema.Dispatch.CorrelatedSubquerySource
import Belay.Sqlite.Model.Programs.Scripts.PlainDeleteRule

set_option doc.verso true

/-- Facts that discharge a plain DELETE filter's row-safety check. -/
register_label_attr delete_row_fact

namespace Belay.Sqlite.Run.DeleteCoverage
open Belay.Sqlite.Model

/-- A comparison of ABS on a stored column with a literal is safe on each input row if
no stored value in that column is the minimum signed integer. The empty row reads NULL. -/
theorem absComparison (rows : List Row) (column : Nat) (op : Comparison) (affinity : Option Affinity)
    (rhs : Value) (collation : Collation) (ctx : Resolved.EvalContext)
    (bounded : ∀ r ∈ rows, r.values.getD column .null ≠ .integer (-(2^63)))
    (row : List Value) (member : row ∈ [] :: rows.map Row.values) :
    (some (Resolved.Expr.compare op affinity (.scalar .abs (.cons (.column column) .nil)) (.literal rhs) collation)).toList.any
      (·.mayFailOn ctx row) = false := by
  rcases List.mem_cons.mp member with empty | stored
  · subst row; cases column <;> rfl
  obtain ⟨r, mem, rfl⟩ := List.mem_map.mp stored
  have ok := bounded r mem
  change ((Resolved.Fault.none.join (Resolved.Fault.ofFunction
    (Resolved.ScalarFunction.apply .abs [r.values.getD column .null]))).join .none != .none || false) = false
  generalize e : r.values.getD column .null = v at *
  cases v <;> try rfl
  rename_i i
  have ne : i ≠ -9223372036854775808 := fun h => ok (congrArg Value.integer h)
  simp [Resolved.ScalarFunction.apply, ne, Resolved.Fault.ofFunction, Resolved.Fault.join]

/-- A comparison of {lit}`json_extract` on a stored column at a literal path with a literal is safe
on every input row if the extraction returns a value for every stored row. -/
theorem jsonComparison (rows : List Row) (column : Nat) (op : Comparison) (affinity : Option Affinity)
    (rhs : Value) (collation : Collation) (path : List UInt8) (ctx : Resolved.EvalContext)
    (extracts : ∀ r ∈ rows, ∃ v, Json.extract (r.values.getD column .null) [.text path] = .ok v)
    (row : List Value) (member : row ∈ [] :: rows.map Row.values) :
    (some (Resolved.Expr.compare op affinity
      (.json .extract (.cons (.column column) (.cons (.literal (.text path)) .nil))) (.literal rhs) collation)).toList.any
      (·.mayFailOn ctx row) = false := by
  rcases List.mem_cons.mp member with empty | stored
  · subst row; cases column <;> rfl
  obtain ⟨r, mem, rfl⟩ := List.mem_map.mp stored
  obtain ⟨v, ok⟩ := extracts r mem
  change ((Resolved.Fault.none.join (Resolved.Fault.ofJson
    (Json.extract (r.values.getD column .null) [.text path]))).join .none != .none || false) = false
  rw [ok]; rfl

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

end Belay.Sqlite.Run.DeleteCoverage
