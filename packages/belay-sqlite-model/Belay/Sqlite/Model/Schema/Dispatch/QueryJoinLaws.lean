import Belay.Sqlite.Model.Schema.Dispatch.QueryFunctions
import Belay.Sqlite.Model.Queries.Select.QueryJoinLaws

set_option doc.verso true

/-! Laws of joined sources (ADR 0012, amendments 2 and 3, "Proofs"; ADR 0013, D5): a query
of one table reads the rows of its table and a query without sources one row with no
cells, every joined row has the width of its sources together, a left or full join keeps
every left row, and a right or full join keeps every row of its source. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every evaluation context, query whose only source is a table, as an inner join without a
condition, and every database, the source rows of the query in the context are the rows of its table in rowid order
({name}`sourceRows`), or none when the table is missing: the query of one table is the
special case of a join. -/
theorem Query.source_single (context : EvalContext) (query : Query) (database : Database) (table : Nat)
    (single : query.sources = [{ kind := .inner, source := .table table, condition := none }]) :
    (query.source context database).map (·.rows) = (database.table table).map sourceRows := by
  simp only [Query.source, single, List.foldlM, QuerySource.join]
  cases database.table table with
  | none => rfl
  | some found =>
    simp [QuerySource.joinTable, joinRows, joinRow, joinMatches, QuerySource.matches, bind, Option.bind, pure]

/-- For every evaluation context, query without sources ({lit}`SELECT` without {lit}`FROM`) and
every database, the source is one row with no cells, without a fault. -/
theorem Query.source_none (context : EvalContext) (query : Query) (database : Database) (none_ : query.sources = []) :
    query.source context database = some { rows := [[]], width := 0, fault := .none } := by
  simp only [Query.source, none_, List.foldlM]
  rfl

/-- For every table that satisfies {name}`Table.RowsWide`, every row of {name}`sourceRows` has
one cell per column. Proof sketch: the scanned rows are a permutation of the table's rows
({name}`Belay.Sqlite.Model.Table.scanRows_perm`), each of which has one cell per column. -/
theorem sourceRows_width {table : Table} (wide : table.RowsWide) :
    ∀ cells ∈ sourceRows table, cells.length = table.shape.columns.length := by
  intro cells member
  obtain ⟨row, sorted, rfl⟩ := List.mem_map.mp member
  exact wide row (table.scanRows_perm.mem_iff.mp sorted)

/-- For every evaluation context, width, left rows of that width, join, and candidate rows of
{lit}`columns` cells each, every row of {name}`joinRows` in the context has the width plus {lit}`columns` cells: a joined
row is a left row followed by a candidate or by NULL padding, or, for a right or full join,
NULL padding of the width followed by a candidate. Proof sketch: a row of the first part has
the width by {name}`joinRow_width`; an added right row is a candidate after the width's
NULLs. Use {name}`sourceRows_width` for the rows of a table with one cell per column. -/
theorem joinRows_width (context : EvalContext) {width : Nat} {left : List (List Value)} {candidates : List (List Value)} {columns : Nat} (join : QuerySource)
    (valid : ∀ cells ∈ candidates, cells.length = columns) (widths : ∀ row ∈ left, row.length = width) :
    ∀ row ∈ joinRows context width left join columns candidates, row.length = width + columns := by
  intro row member
  unfold joinRows at member
  rcases List.mem_append.mp member with joined | added
  · obtain ⟨leftRow, leftMember, joined⟩ := List.mem_flatMap.mp joined
    exact joinRow_width context join valid (widths leftRow leftMember) row joined
  · cases kind : join.kind <;> simp only [kind, List.not_mem_nil] at added
    all_goals
      obtain ⟨cells, unmatched, rfl⟩ := List.mem_map.mp added
      simp [valid cells (List.mem_filter.mp unmatched).1]

end Belay.Sqlite.Model.Resolved
