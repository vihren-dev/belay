import Belay.Sqlite.Model.UpsertInserted

set_option doc.verso true

/-! The support check of an upsert of rows that meet every constraint (ADR 0017, S6). The upsert is ready
({lit}`LiteralData.upsertReady`) when the table is ready, its rowid alias is an integer column, every row
has one stored cell for each column, each clause assigns existing columns, and the rowids that the upsert
reaches are signed 64-bit integers. For rows that meet every constraint, the last test follows from the
rowids of the final table: every rowid that the upsert reaches is a rowid of that table. -/

namespace Belay.Sqlite.Model
namespace LiteralData

/-- For every context, keys, policy, clauses, table and supplied rows with the premises of
{name}`upsertSummary_inserted`: if the rowids of the table after {name}`inserted` are bounded, the reached
rows of the upsert are bounded ({name}`upsertBounded`). Proof sketch: induction on the rows as for
{name}`upsertSummary_inserted`; the rowid of the proposed row and the rows of the table after it are rows of
the final table. -/
theorem upsertBounded_inserted (context : Resolved.EvalContext) (keys : List UniqueKey)
    (policy : Resolved.ConflictPolicy) (clauses : List Resolved.ConflictClause) :
    ∀ (table : Table) (rows : List (List Value)), (∀ values ∈ rows, aliasMismatch table.shape values = false) →
      constraints keys (inserted table rows) = true → rowidsDistinct (inserted table rows) = true →
      (inserted table rows).rows.all (fun row => boundedInteger row.rowid) = true →
      upsertBounded (upsertSteps context keys policy clauses table rows) = true
  | table, [], _, _, _, _ => by simp [upsertSteps, upsertBounded]
  | table, values :: rest, alias, passes, distinct, bounded => by
    have whole : inserted table (values :: rest) = inserted (insertRow table values) rest := rfl
    rw [whole] at passes distinct bounded
    obtain ⟨added, appended⟩ := inserted_rows_prefix (insertRow table values) rest
    have shape : (inserted (insertRow table values) rest).shape = (insertRow table values).shape :=
      shape_inserted _ _
    have first := upsertRow_insertRow context keys policy clauses table values
      (alias values (List.mem_cons_self ..)) (constraints_of_appended shape appended passes) (by
        simp only [rowidsDistinct, decide_eq_true_eq] at distinct ⊢
        rw [appended, List.map_append] at distinct
        exact (List.pairwise_append.mp distinct).1)
    have later := upsertBounded_inserted context keys policy clauses (insertRow table values) rest
      (fun other member => by simpa [insertRow] using alias other (List.mem_cons_of_mem _ member)) passes distinct
      bounded
    rw [appended, List.all_append, Bool.and_eq_true] at bounded
    simp only [upsertSteps, first, upsertBounded, List.all_cons, Bool.and_eq_true] at later ⊢
    refine ⟨⟨?_, bounded.1⟩, later⟩
    exact List.all_eq_true.mp bounded.1 (proposedRow table values) (by simp [insertRow, proposedRow])

end LiteralData
end Belay.Sqlite.Model
