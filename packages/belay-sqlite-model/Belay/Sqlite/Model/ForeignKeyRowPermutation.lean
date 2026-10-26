import Belay.Sqlite.Model.ForeignKeyParentUnique

set_option doc.verso true

/-! Foreign-key observations and unique-key facts under row permutation. -/

namespace Belay.Sqlite.Model

/-- For every parent lookup without a self shortcut, permuting the parent rows keeps
the result. Proof sketch: lookup is the same existential test over the permuted list. -/
theorem parentFound_perm (parent : CatalogTable) (key : ParentKey) (link : ForeignKeyLink)
    (values : List Value) {rows other : List Row} (permuted : rows.Perm other) :
    parentFound parent key link values rows none = parentFound parent key link values other none := by
  rw [parentFound_any parent key link values rows, parentFound_any parent key link values other]
  exact permuted.any_eq

/-- For every two databases with equal catalogs and pairwise permuted table rows, each
link has equal satisfaction on every supplied child row. Proof sketch: parent lookup ignores
row order, while the NULL test and selected mapping are unchanged. -/
theorem ForeignKeyLink.satisfied_rows_perm {before after : Database}
    (catalog : after.catalog = before.catalog) (rows : ∀ position, (before.rowsAt position).Perm (after.rowsAt position))
    (link : ForeignKeyLink) (row : Row) : link.satisfied before row = link.satisfied after row := by
  simp only [ForeignKeyLink.satisfied, catalog]
  cases selected : link.parent with
  | missing | mismatch other => rfl
  | located other key =>
    cases atShape : before.catalog.tableAt other with
    | none => simp [atShape]
    | some shape => simp only [atShape, parentFound_perm shape key link row.values (rows other)]

/-- For every two databases with equal catalogs and pairwise permuted table rows, their
total FK violation counts are equal. Proof sketch: satisfaction is unchanged and permutation
preserves each child-row count. -/
theorem Database.foreignKeyViolations_rows_perm {before after : Database}
    (catalog : after.catalog = before.catalog) (rows : ∀ position, (before.rowsAt position).Perm (after.rowsAt position)) :
    before.foreignKeyViolations = after.foreignKeyViolations := by
  unfold Database.foreignKeyViolations
  rw [catalog]
  congr 1
  apply List.map_congr_left
  intro link _
  have equal : (fun row => !link.satisfied before row) = (fun row => !link.satisfied after row) := by
    funext row
    rw [ForeignKeyLink.satisfied_rows_perm catalog rows]
  rw [equal]
  exact (rows link.child).countP_eq _

/-- For every unique-key list and two tables with permuted rows, uniqueness of the first
implies uniqueness of the second. Shapes need not agree: this fact uses the supplied keys.
Proof sketch: pairwise unequal-key checks are symmetric and invariant under permutation. -/
theorem Table.KeysUnique.perm {keys : List UniqueKey} {table other : Table}
    (unique : table.KeysUnique keys) (permuted : table.rows.Perm other.rows) : other.KeysUnique keys := by
  intro key member
  apply (unique key member).perm permuted
  intro first second different
  apply Bool.eq_false_iff.mpr
  intro equal
  have reverse := LiteralData.keyEqual_symm equal
  rw [different] at reverse
  contradiction

/-- For every list with distinct rowids, a member old row and any new row, replacing
the old rowid in place gives a permutation of removing it and appending the new row.
Proof sketch: distinctness leaves exactly one replacement position; move that row to the end. -/
theorem replaceRow_perm_append (rows : List Row) (old new : Row) (distinct : (rows.map Row.rowid).Nodup)
    (member : old ∈ rows) :
    (rows.map fun row => if row.rowid == old.rowid then new else row).Perm
      ((rows.filter (·.rowid != old.rowid)) ++ [new]) := by
  induction rows with
  | nil => contradiction
  | cons first rest induction =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    by_cases same : first.rowid = old.rowid
    · have separated : ∀ row ∈ rest, row.rowid ≠ old.rowid := by
        intro row member equal
        exact distinct.1 (List.mem_map.mpr ⟨row, member, equal.trans same.symm⟩)
      have filtered : rest.filter (·.rowid != old.rowid) = rest :=
        List.filter_eq_self.mpr (fun row member => by simpa using separated row member)
      have mapped : (rest.map fun row => if row.rowid == old.rowid then new else row) = rest := by
        calc
          _ = rest.map id := by
            apply List.map_congr_left
            intro row member
            simp [separated row member]
          _ = rest := List.map_id rest
      simp only [List.map_cons, same, beq_self_eq_true, ite_true, List.filter_cons,
        bne_self_eq_false, Bool.false_eq_true, ite_false, filtered, mapped]
      simpa only [List.singleton_append] using (List.perm_append_comm (l₁ := [new]) (l₂ := rest))
    · have oldIn : old ∈ rest := by
        rcases List.mem_cons.mp member with equal | later
        · subst first; contradiction
        · exact later
      have remaining := induction distinct.2 oldIn
      simpa [same] using remaining.cons first

/-- For every aligned present table, replacing its rows with either of two permuted
lists gives permuted rows at every database position. Proof sketch: the target has the supplied
permutation, and every other table is unchanged. -/
theorem Database.rowsAt_setRows_perm {database : Database} {position : Nat} {table : Table}
    (present : database.table position = some table) (aligned : position < database.rows.length)
    {rows other : List Row} (permuted : rows.Perm other) (target : Nat) :
    ((database.setRows position rows).rowsAt target).Perm ((database.setRows position other).rowsAt target) := by
  by_cases same : target = position
  · subst target
    simpa only [Database.rowsAt, Database.table_setRows _ present aligned, Option.map_some, Option.getD_some] using permuted
  · simp only [Database.rowsAt, Database.table_setRows_other _ _ same]
    exact List.Perm.refl _

end Belay.Sqlite.Model
