import Belay.Sqlite.Model.ForeignKeyEngineFacts
import Belay.Sqlite.Model.ForeignKeyChangeCoverage
import Belay.Sqlite.Model.ForeignKeyUpdateCoverage
import Belay.Sqlite.Model.ForeignKeyUpdateBound

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For a good input and checked replacement of an existing row, actual old/new
check results bound the replacement's violation count by the final counter. Catalog
comparison facts and cell/rowid coverage justify omitted checks. If SQLite retains a stale
row for a low-level update, each processed parent link must have another child table.
Proof sketch: use the exact frame at level zero; otherwise apply the replacement bound,
with assignment coverage for omitted checks and agreement for retained stale child rows. -/
theorem updateChecks_covered_bound {profile : Profile} {catalog : Catalog} {state before checked : KeyState}
    {position : Nat} {name : Identifier} {shape : CatalogTable} {table : Table}
    (good : KeyState.ForeignKeyInvariant profile catalog state) (facts : catalog.ForeignKeyComparisons)
    (object : catalog[position]? = some {name, entry := .table shape})
    (present : (state.database catalog).table position = some table)
    (change : Row → Row) (changed : List Nat) (covers : RowChange.Covers shape changed change)
    (old : Row) (member : old ∈ table.rows)
    (passed : checkedUpdate catalog state position old (change old) = .ok ())
    (noStaleScan : (updateLevel catalog.foreignKeyLinks position name shape changed ≤ 1 ∧
      (shape.rowidAlias.any changed.contains || (shape.withoutRowid && shape.primaryKey.any changed.contains)) = false) →
      ∀ link ∈ (parentLinks catalog.foreignKeyLinks position).filter (·.key.parentChanged shape changed), link.child ≠ position)
    (oldResult : (if updateLevel catalog.foreignKeyLinks position name shape changed != 0 then
      oldSteps catalog state position old
        ((childLinks catalog.foreignKeyLinks position).filter fun link => link.key.childChanged changed || link.key.selfReferences name)
        ((parentLinks catalog.foreignKeyLinks position).filter (·.key.parentChanged shape changed)) false else pure state) = .ok before)
    (newResult : (if updateLevel catalog.foreignKeyLinks position name shape changed != 0 then
      newSteps catalog (before.changeRows position (fun rows => rows.filter (·.rowid != old.rowid))) position (change old)
        ((childLinks catalog.foreignKeyLinks position).filter fun link => link.key.childChanged changed || link.key.selfReferences name)
        ((parentLinks catalog.foreignKeyLinks position).filter (·.key.parentChanged shape changed)) true
        (if updateLevel catalog.foreignKeyLinks position name shape changed ≤ 1 &&
          !(shape.rowidAlias.any changed.contains || (shape.withoutRowid && shape.primaryKey.any changed.contains)) then some old else none)
        changed else pure (before.changeRows position (fun rows => rows.filter (·.rowid != old.rowid)))) = .ok checked) :
    (((state.database catalog).setRows position (LiteralData.replaceRow table old (change old)).rows).foreignKeyViolations : Int) ≤
      checked.counter := by
  have atShape : catalog.tableAt position = some shape := by simp only [Catalog.tableAt, object]
  have sameShape : table.shape = shape := by
    have other := KeyState.table_shape present
    rw [atShape, Option.some.injEq] at other
    exact other.symm
  obtain ⟨constraints, admitted⟩ := checkedUpdate_ok passed present
  have oldWide : old.values.length = shape.columns.length := by
    rw [← sameShape]
    exact good.1.1.rowsWide position table present old member
  have oldAliased : old.Aliased shape.rowidAlias := by
    rw [← sameShape]
    exact good.1.1.rowsAliased position table present old member
  have newFacts := (LiteralData.rowAdmitted_iff _ _).mp admitted
  rw [sameShape] at newFacts
  have aliasPrimary := fun alias (found : shape.rowidAlias = some alias) =>
    CatalogTable.alias_primaryKey (good.1.1.catalogSupported.tableSupported atShape) found
  have coverage := covers.cells old oldWide oldAliased
  by_cases zero : updateLevel catalog.foreignKeyLinks position name shape changed = 0
  · simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq] at oldResult newResult
    subst before
    subst checked
    have unchanged := Catalog.updateLevel_zero_agrees atShape zero aliasPrimary oldAliased newFacts.2.2.2 coverage
    have count := Database.foreignKeyViolations_replace_unchanged present
      (KeyState.table_aligned good.1.1.rowsShaped present) (good.1.1.rowidsDistinct position table present)
      old (change old) member unchanged.1 unchanged.2
    rw [count]
    exact good.2
  · simp only [bne_iff_ne] at oldResult newResult
    rw [ite_eq_left zero] at oldResult newResult
    apply updateChecks_replace_bound good.2 present
      (KeyState.table_aligned good.1.1.rowsShaped present) (good.1.1.rowidsDistinct position table present)
      good.1.1.rowsStored old (change old) member (by simpa only [sameShape] using newFacts.2.2.1)
      (keysUniqueFacts.constraints _ _ _ constraints) (passed_rowidsDistinct constraints)
      (fun link inside key child located childAt => facts.scans link inside position key child.shape table.shape
        located (KeyState.table_shape childAt) (KeyState.table_shape present))
      (fun link inside pairs located => facts.unique link inside position pairs table.shape located (KeyState.table_shape present))
      (fun link => link.key.childChanged changed || link.key.selfReferences name)
      (fun link => link.key.parentChanged shape changed)
      (fun link inside ignored => Catalog.updateChildren_unchanged object inside ignored (fun cell outside => coverage cell (.inl outside)))
      (fun link inside ignored => Catalog.updateParents_unchanged atShape inside ignored aliasPrimary oldAliased newFacts.2.2.2 coverage)
      (if updateLevel catalog.foreignKeyLinks position name shape changed ≤ 1 &&
        !(shape.rowidAlias.any changed.contains || (shape.withoutRowid && shape.primaryKey.any changed.contains)) then some old else none)
      changed ?_ ?_ ?_ oldResult newResult
    · intro link inside key located
      have selected := List.mem_filter.mp inside |>.1
      have childAt : link.child = position := by simpa [childLinks] using (List.mem_filter.mp (List.mem_reverse.mp selected)).2
      have inLinks := (List.mem_filter.mp (List.mem_reverse.mp selected)).1
      simpa only [sameShape] using facts.self link inLinks key shape (by simpa only [childAt] using located) (by simpa only [childAt] using atShape)
    · intro link _ key _ previous member
      split at member
      · rename_i retained
        have notMoved : (shape.rowidAlias.any changed.contains ||
            (shape.withoutRowid && shape.primaryKey.any changed.contains)) = false := by
          simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp retained).2
        have unmoved : shape.rowidAlias.any changed.contains = false := (Bool.or_eq_false_iff.mp notMoved).1
        apply staleRows_agree key old (change old) changed
          (covers.rowid old oldWide oldAliased unmoved).symm (fun cell outside => coverage cell (.inl outside)) previous member
      · cases key <;> simp [staleRows] at member
    · split
      · rename_i retained
        right
        apply noStaleScan
        exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp retained).1, by simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp retained).2⟩
      · exact .inl rfl

end Belay.Sqlite.Model
