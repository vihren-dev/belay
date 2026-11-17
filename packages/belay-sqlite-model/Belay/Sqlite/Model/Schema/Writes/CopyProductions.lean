import Belay.Sqlite.Model.Queries.Evaluation.CopyScanOrders
import Belay.Sqlite.Model.Schema.Writes.PlainScanProductions
import Belay.Sqlite.Model.Tooling.Counterexamples.CopyInsertRows

set_option doc.verso true

/-! A query that copies every source column yields the source cells, in each
order in which the database can scan the source table. -/

namespace Belay.Sqlite.Model

/-- A plain resolved SELECT of all columns of one table in their original order.
The caller supplies SQLite's result column names. -/
def Resolved.Query.copyOf (position width : Nat) (names : List String) : Resolved.Query :=
  .simple [.first position] none ((List.range width).map fun i => .scalar (.column i)) names

/-- For any admitted source table, the productions of its copy query are the
rows of its access orders, without source errors. Each distinct result occurs
once. The clock and parameters can vary in the quiet context. Proof sketch:
a simple projection contains no fallible calls. Each scan permutes the rows,
so its cells have the source width and projecting all its columns is identity. -/
theorem Resolved.Query.productions_copyOf (context : Resolved.EvalContext) (database : Database) (position : Nat)
    (table : Table) (names : List String) (streaming : Bool) (quiet : context.Quiet)
    (present : database.table position = some table) (admitted : table.Admitted) :
    (copyOf position table.shape.columns.length names).productions context database streaming =
      some (((Table.accessOrders database.catalog position table).map fun order =>
        ({ rows := order.map Row.values, failure := none } : SourceProduction)).eraseDups) := by
  let query := copyOf position table.shape.columns.length names
  have plain : query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true := by
    simp [query, copyOf, Resolved.Query.simple, Resolved.Query.expressions, Resolved.Query.keptExpressions,
      Resolved.QuerySource.first, Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands,
      List.all_eq_true, Resolved.Expr.any, Resolved.Expr.isFallibleCall]
  rw [query.productions_scan context database position table streaming rfl rfl rfl rfl rfl rfl rfl rfl
    plain quiet present (by rfl)]
  congr 2
  apply List.map_congr_left
  intro order member
  have perm := Table.accessOrders_perm database.catalog position table admitted.rowidsDistinct order member
  have wide : ∀ cells ∈ order.map Row.values, cells.length = table.shape.columns.length := by
    simpa using fun row m => admitted.rowsWide row (perm.mem_iff.mp m)
  rw [Resolved.Query.results_copy (query := query) rfl rfl rfl rfl rfl rfl context _ rfl rfl _ wide]

end Belay.Sqlite.Model
