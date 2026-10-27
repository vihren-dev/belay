import Belay.Sqlite.Model.DatabaseConstraintChecks
import Belay.Sqlite.Model.RowLocalWrites
import Belay.Sqlite.Model.UpsertRun
import Belay.Sqlite.Model.LiteralPreservationLaws

set_option doc.verso true

/-! The upsert of rows that meet every constraint (ADR 0017, S6). The laws of the existing modules say
what a successful upsert keeps. This module gives the other direction: when the table after appending
all supplied rows ({lit}`LiteralData.inserted`) meets the constraints of the table and has distinct
rowids, no row of the upsert fails, no clause handles a row, no conflict algorithm acts, and the result of
the upsert is that table, with the appended rows as the written rows. The check on the final table alone
is enough, because every table before it is a prefix of its rows. -/

namespace Belay.Sqlite.Model
namespace LiteralData

/-- For every table and supplied rows, the rows of {name}`inserted` are the rows of the table followed by
some added rows. Proof sketch: induction on the supplied rows; one {name}`insertRow` appends a row. -/
theorem inserted_rows_prefix (table : Table) (rows : List (List Value)) :
    ∃ added, (inserted table rows).rows = table.rows ++ added := by
  induction rows generalizing table with
  | nil => exact ⟨[], by simp [inserted]⟩
  | cons values rest ih =>
    obtain ⟨added, same⟩ := ih (insertRow table values)
    exact ⟨_ :: added, by simp [inserted, insertRow] at same ⊢; exact same⟩

/-- For every key and rows with a conflict-free extension: if the longer list has no conflicting pair, the
prefix has none. Proof sketch: {name}`uniqueRows_iff` and the sublist of a pairwise list. -/
theorem uniqueRows_of_append {key : UniqueKey} {rows added : List Row}
    (unique : uniqueRows key (rows ++ added) = true) : uniqueRows key rows = true := by
  rw [uniqueRows_iff] at unique ⊢
  exact unique.sublist (List.sublist_append_left ..)

/-- For every keys and two tables with the same catalog entry where the rows of the second are those of
the first followed by added rows: if the second table passes {name}`constraints`, so does the first. In
plain words, a prefix of the rows of a table that meets the constraints meets them. Proof sketch: the
NOT NULL, type and CHECK checks read one row at a time ({name}`List.all_append`), and
{name}`uniqueRows_of_append` handles the keys. -/
theorem constraints_of_appended {keys : List UniqueKey} {table final : Table} {added : List Row}
    (shape : final.shape = table.shape) (appended : final.rows = table.rows ++ added)
    (passes : constraints keys final = true) : constraints keys table = true := by
  simp only [constraints, notNullRows, typedRows, checkedRows, keysUnique, Bool.and_eq_true, shape, appended,
    List.all_append] at passes ⊢
  exact ⟨⟨⟨passes.1.1.1.1, passes.1.1.2.1⟩, passes.1.2.1⟩,
    List.all_eq_true.mpr fun key member => uniqueRows_of_append (List.all_eq_true.mp passes.2 key member)⟩

/-- For every key, rows and proposed row: if the rows followed by the proposed row have no conflicting pair
on the key, no row conflicts with the proposed row. Proof sketch: {name}`uniqueRows_iff` and the pairs of
an appended list ({name}`List.pairwise_append`). -/
theorem keyEqual_false_of_unique {key : UniqueKey} {rows : List Row} {proposed : Row}
    (unique : uniqueRows key (rows ++ [proposed]) = true) : ∀ row ∈ rows, keyEqual key row proposed = false := by
  rw [uniqueRows_iff, List.pairwise_append] at unique
  exact fun row member => unique.2.2 row member proposed (List.mem_singleton_self _)

/-- For every keys and clause, a key that the clause checks is a key of the table. Proof sketch: the
clause checks every key, or the first key with its columns ({name}`List.mem_of_find?_eq_some`). -/
theorem mem_of_mem_clauseKeys {keys : List UniqueKey} {clause : Resolved.ConflictClause} {key : UniqueKey}
    (member : key ∈ clauseKeys keys clause) : key ∈ keys := by
  unfold clauseKeys at member
  cases target : clause.target with
  | none => simpa [target] using member
  | some columns =>
    simp only [target, Option.mem_toList] at member
    exact List.mem_of_find?_eq_some member

/-- For every keys, conflict algorithms, table and proposed row, when no row of the table conflicts with the
proposed row on any key and the table with the proposed row appended passes {name}`checkedRow`'s test:
{name}`insertChecked` appends the proposed row, with no key blocking and no row replaced. Proof sketch:
{name}`blockingKey` finds no key that a row conflicts on, {name}`replaced` removes no row, and
{name}`checkedRow` passes. -/
theorem insertChecked_of_fresh (keys : List UniqueKey) (algorithms : List ConflictAlgorithm) (table : Table)
    (proposed : Row) (fresh : ∀ key ∈ keys, ∀ row ∈ table.rows, keyEqual key row proposed = false)
    (passes : constraints keys { table with rows := table.rows ++ [proposed] } = true)
    (distinct : rowidsDistinct { table with rows := table.rows ++ [proposed] } = true) :
    insertChecked keys algorithms table proposed =
      .ok ({ table with rows := table.rows ++ [proposed] }, some proposed) := by
  have free : ∀ (index : Nat) (key : UniqueKey), keys[index]? = some key →
      ∀ row ∈ table.rows, keyEqual key row proposed = false := by
    intro index key keyMember row rowMember
    exact fresh key (List.mem_of_getElem? keyMember) row rowMember
  have unblocked : blockingKey keys algorithms table proposed = none := by
    unfold blockingKey
    rw [List.find?_eq_none]
    intro index _
    have : conflictsAt keys table proposed index = false := by
      unfold conflictsAt
      cases lookup : keys[index]? with
      | none => rfl
      | some key => simpa using free index key lookup
    simp [this]
  have kept : replaced keys algorithms table proposed = table := by
    unfold replaced
    congr
    apply List.filter_eq_self.mpr
    intro row rowMember
    simp only [Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true]
    intro index _ again
    cases lookup : keys[index]? with
    | none => simp [lookup] at again
    | some key => simp [lookup, free index key lookup row rowMember] at again
  unfold insertChecked checkedRow
  simp [unblocked, kept, passes, distinct]

/-- For every context, keys, policy, clauses, table and supplied cells: if the row has no rowid alias
mismatch, and the table after {name}`insertRow` passes {name}`constraints` and has distinct rowids, then
{name}`upsertRow` appends the proposed row and writes it. In plain words, a row that meets every
constraint is inserted whatever the clauses and the conflict algorithms say, because nothing conflicts with
it. Proof sketch: the new row is the last row of the table after the insertion, so the NOT NULL, type and
CHECK tests pass for it; no row conflicts with it on any key, so no clause handles it, no key blocks it, and
no row is replaced; the final check of {name}`checkedRow` is the premise. -/
theorem upsertRow_insertRow (context : Resolved.EvalContext) (keys : List UniqueKey)
    (policy : Resolved.ConflictPolicy) (clauses : List Resolved.ConflictClause) (table : Table)
    (values : List Value) (alias : aliasMismatch table.shape values = false)
    (passes : constraints keys (insertRow table values) = true)
    (distinct : rowidsDistinct (insertRow table values) = true) :
    upsertRow context keys policy clauses table values = .ok (insertRow table values, some (proposedRow table values)) := by
  have member : proposedRow table values ∈ (insertRow table values).rows := by simp [insertRow, proposedRow]
  have wholePasses := passes
  simp only [constraints, notNullRows, typedRows, checkedRows, keysUnique, Bool.and_eq_true] at passes
  obtain ⟨⟨⟨nonNull, typed⟩, checked⟩, unique⟩ := passes
  have fresh : ∀ key ∈ keys, ∀ row ∈ table.rows, keyEqual key row (proposedRow table values) = false :=
    fun key keyMember => keyEqual_false_of_unique (List.all_eq_true.mp unique key keyMember)
  have shape : (insertRow table values).shape = table.shape := rfl
  rw [shape] at nonNull typed checked
  have nullFree : nullColumn table.shape.columns (proposedRow table values).values = none := by
    have row := List.all_eq_true.mp nonNull _ member
    unfold nullColumn
    rw [List.findIdx?_eq_none_iff]
    intro ⟨column, value⟩ inZip
    have := List.all_eq_true.mp row (column, value) inZip
    simp only [Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this ⊢
    rcases this with notNull | present
    · simp [notNull]
    · simp [present]
  have typesOk : typesFit table.shape (proposedRow table values) = true := List.all_eq_true.mp typed _ member
  have checksOk : checksHold table.shape (proposedRow table values) = true := by
    simpa [checksHold] using List.all_eq_true.mp checked _ member
  have unhandled : handlingClause keys clauses table (proposedRow table values) = none := by
    unfold handlingClause
    rw [List.findSome?_eq_none_iff]
    intro clause _
    simp only [conflictingRow, Option.map_eq_none_iff, List.find?_eq_none, Bool.not_eq_true, List.any_eq_false]
    intro row rowMember key keyMember
    exact fresh key (mem_of_mem_clauseKeys keyMember) row rowMember
  unfold upsertRow
  simp only [alias, Bool.false_eq_true, ite_false, nullFree, typesOk, checksOk, unhandled, Bool.not_true, Bool.false_eq_true, ite_false]
  exact insertChecked_of_fresh keys policy.keys table (proposedRow table values) fresh
    wholePasses distinct

/-- For every table and supplied rows, {name}`inserted` keeps the catalog entry of the table. It is
{name}`LiteralData.inserted_shape` in the namespace of this module. -/
theorem shape_inserted (table : Table) (rows : List (List Value)) : (inserted table rows).shape = table.shape :=
  Belay.Sqlite.Model.LiteralData.inserted_shape table rows

/-- For every context, keys, policy, clauses, table and supplied rows: if no row has a rowid alias mismatch,
and the table after {name}`inserted` passes {name}`constraints` and has distinct rowids, then the reached rows of
the upsert ({name}`upsertSteps`) summarize ({name}`upsertSummary`) to that table, with the appended rows
as the written rows. In plain words, rows that meet every constraint are inserted one after the other, and
no row fails, whatever the clauses and the conflict algorithms say. Proof sketch: induction on the rows; the
table after the first row is a prefix of the final table, so {name}`constraints_of_appended` and the prefix of
distinct rowids give the premises of {name}`upsertRow_insertRow` for the first row. -/
theorem upsertSummary_inserted (context : Resolved.EvalContext) (keys : List UniqueKey)
    (policy : Resolved.ConflictPolicy) (clauses : List Resolved.ConflictClause) :
    ∀ (table : Table) (rows : List (List Value)), (∀ values ∈ rows, aliasMismatch table.shape values = false) →
      constraints keys (inserted table rows) = true → rowidsDistinct (inserted table rows) = true →
      upsertSummary table (upsertSteps context keys policy clauses table rows) =
        .ok (inserted table rows, (inserted table rows).rows.drop table.rows.length)
  | table, [], _, _, _ => by simp [upsertSteps, upsertSummary, inserted]
  | table, values :: rest, alias, passes, distinct => by
    have whole : inserted table (values :: rest) = inserted (insertRow table values) rest := rfl
    rw [whole] at passes distinct ⊢
    obtain ⟨added, appended⟩ := inserted_rows_prefix (insertRow table values) rest
    have shape : (inserted (insertRow table values) rest).shape = (insertRow table values).shape :=
      shape_inserted _ _
    have first := upsertRow_insertRow context keys policy clauses table values
      (alias values (List.mem_cons_self ..)) (constraints_of_appended shape appended passes) (by
        simp only [rowidsDistinct, decide_eq_true_eq] at distinct ⊢
        rw [appended, List.map_append] at distinct
        exact (List.pairwise_append.mp distinct).1)
    have later := upsertSummary_inserted context keys policy clauses (insertRow table values) rest
      (fun other member => by simpa [insertRow] using alias other (List.mem_cons_of_mem _ member)) passes distinct
    simp only [upsertSteps, first, upsertSummary, later]
    congr 2
    rw [appended]
    simp [insertRow]
    rfl

end LiteralData
end Belay.Sqlite.Model
