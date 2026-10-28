import Belay.Sqlite.Model.QueryJoinLaws
import Belay.Sqlite.Model.DatabaseLookup

set_option doc.verso true

/-! The source rows of a query over one table (ADR 0017, S4): a query whose only source
is that table reads its rows in scan order (rowid order, or primary-key order for a
{lit}`WITHOUT ROWID` table), with no fault. -/

namespace Belay.Sqlite.Model

/-- For every evaluation context, query whose only source is the table at a position as an inner
join without a condition ({name}`Resolved.QuerySource.first`), and database that has the table at
that position, the source rows are the rows of the table in scan order (rowid order, or primary-key order
for a {lit}`WITHOUT ROWID` table), the width field of the result is the number of columns of the table, and
the fault is none. The lemma does not say that each row has that many cells. Proof sketch:
{name}`Resolved.Query.source_single` gives the rows; the width and the fault come from the definition of the join. -/
theorem Resolved.Query.source_first (context : Resolved.EvalContext) (query : Resolved.Query) (database : Database)
    (position : Nat) (table : Table) (sources : query.sources = [Resolved.QuerySource.first position])
    (present : database.table position = some table) :
    query.source context database =
      some { rows := sourceRows table, width := table.shape.columns.length, fault := .none } := by
  have rows := Resolved.Query.source_single context query database position sources
  simp only [Resolved.Query.source, sources, List.foldlM, Resolved.QuerySource.join, Resolved.QuerySource.joinTable, Resolved.QuerySource.first, present,
    Option.map_some, bind, Option.bind, pure, Option.some.injEq] at rows ⊢
  rw [rows, Nat.zero_add]

end Belay.Sqlite.Model
