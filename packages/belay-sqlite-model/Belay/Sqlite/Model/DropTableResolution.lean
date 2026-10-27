import Belay.Sqlite.Model.CreateTableStepLaws

set_option doc.verso true

/-! What the resolution of DROP TABLE says about the statement it gives (ADR 0017, S6): the positions
that it drops, and the rules that it carries. The step laws of DROP TABLE use these facts to find the
tables that the statement does not touch, and to exclude the effects of foreign keys on them. -/

namespace Belay.Sqlite.Model

/-- For every catalog, name and flag, and every statement that {name}`resolveDropTable` gives: if the
statement is a drop with positions, then it carries no rules, and its positions are the objects of the
table that the name finds ({name}`Catalog.tableObjects`) or none at all. In plain words, a resolved
DROP TABLE drops one table found by name together with its indexes and triggers, or nothing. Proof
sketch: unfold the resolver; a schema table or a missing table gives a prepare error or the empty drop,
and a found table gives the drop of its objects. -/
theorem resolveDropTable_drop {catalog : Catalog} {name : Identifier} {ifExists : Bool} {after : Catalog}
    {positions : List Nat} {rules : Option Resolved.WriteRules}
    (resolved : resolveDropTable catalog name ifExists = .ok (.drop positions rules, after)) :
    rules = none ∧ (positions = [] ∨ ∃ position table, catalog.findTable name = some (position, table) ∧
      positions = catalog.tableObjects position) := by
  unfold resolveDropTable at resolved
  split at resolved
  · simp [prepareError] at resolved
  · split at resolved
    · rename_i position table found
      simp only [Except.ok.injEq, Prod.mk.injEq, Resolved.Statement.drop.injEq] at resolved
      obtain ⟨⟨rfl, rfl⟩, -⟩ := resolved
      exact ⟨rfl, .inr ⟨_, _, found, rfl⟩⟩
    · split at resolved
      · simp [prepareError] at resolved
      · split at resolved
        · simp only [Except.ok.injEq, Prod.mk.injEq, Resolved.Statement.drop.injEq] at resolved
          obtain ⟨⟨rfl, rfl⟩, -⟩ := resolved
          exact ⟨rfl, .inl rfl⟩
        · simp [prepareError] at resolved


/-- For every catalog, name, flag and result of {name}`resolveDropTable`: the statement is a drop, or a
prepare error. Proof sketch: every branch of the resolver gives one of the two. -/
theorem resolveDropTable_shape {catalog : Catalog} {name : Identifier} {ifExists : Bool} {statement : Resolved.Statement}
    {after : Catalog} (resolved : resolveDropTable catalog name ifExists = .ok (statement, after)) :
    (∃ positions rules, statement = .drop positions rules) ∨ ∃ error, statement = .prepareError error := by
  unfold resolveDropTable at resolved
  repeat' split at resolved
  all_goals first
    | (simp only [prepareError, Except.ok.injEq, Prod.mk.injEq] at resolved; exact .inr ⟨_, resolved.1.symm⟩)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at resolved; exact .inl ⟨_, _, resolved.1.symm⟩)

/-- For every context, state with foreign keys off, positions, rules and catalog: resolving a drop as a
write gives the drop itself, with the catalog after it and nothing else changed. In plain words, with
enforcement off DROP TABLE gets no rules: it checks no foreign key and runs no trigger program, because
the DELETE that it implies fires no trigger. Proof sketch: with foreign keys off the check of keys is
skipped, {name}`triggerPrograms` has no request for a drop ({name}`Resolved.Statement.fireRequest`), a
drop reads no counter, and a write without keys and programs gets no rules. -/
theorem ResolveState.withWrite_drop_off (context : ResolveContext) (state : ResolveState) (positions : List Nat)
    (rules : Option Resolved.WriteRules) (catalog : Catalog) (off : state.foreignKeys = false) :
    state.withWrite context (.ok (.drop positions rules, catalog)) =
      .ok (.drop positions rules, { state with catalog }) := by
  have programs : triggerPrograms context state.catalog false state.recursiveTriggers (.drop positions rules) =
      .ok (.ok []) := by
    cases positions <;> simp [triggerPrograms, Resolved.Statement.fireRequest, pure, Except.pure]
  simp [ResolveState.withWrite, ResolveState.withCatalog, off, programs, Except.map, bind, Except.bind, pure,
    Except.pure, Resolved.Statement.readsCounterInWrite, Resolved.Statement.counterReads]

/-- For every context, state with foreign keys off and prepare error: resolving the prepare error as a
write gives the prepare error. Proof sketch: as {name}`ResolveState.withWrite_drop_off`; a prepare error
writes no row. -/
theorem ResolveState.withWrite_prepareError_off (context : ResolveContext) (state : ResolveState)
    (error : PrepareError) (catalog : Catalog) (off : state.foreignKeys = false) :
    state.withWrite context (.ok (.prepareError error, catalog)) =
      .ok (.prepareError error, { state with catalog }) := by
  have programs : triggerPrograms context state.catalog false state.recursiveTriggers (.prepareError error) =
      .ok (.ok []) := by
    simp [triggerPrograms, Resolved.Statement.fireRequest, pure, Except.pure]
  simp [ResolveState.withWrite, ResolveState.withCatalog, off, programs, Except.map, bind, Except.bind, pure,
    Except.pure, Resolved.Statement.readsCounterInWrite, Resolved.Statement.counterReads]

/-- For every context, state with foreign keys off, DROP TABLE and drop that it resolves to: the drop
carries no rules, and its positions are none or the objects of the table that the name finds. In plain
words, a DROP TABLE on a connection with foreign keys off runs as the plain drop of the model. Proof
sketch: {name}`ResolveState.withWrite_drop_off` removes the write wrapper, and
{name}`resolveDropTable_drop` reads the drop. -/
theorem resolveStatement_dropTable_off (context : ResolveContext) (state after : ResolveState) (name : Identifier)
    (ifExists : Bool) {positions : List Nat} {rules : Option Resolved.WriteRules} (off : state.foreignKeys = false)
    (found : resolveStatement context state (.dropTable name ifExists) = .ok (.drop positions rules, after)) :
    rules = none ∧ (positions = [] ∨ ∃ position table, state.catalog.findTable name = some (position, table) ∧
      positions = state.catalog.tableObjects position) := by
  simp only [statement_arms] at found
  cases resolution : resolveDropTable state.catalog name ifExists with
  | error restriction =>
    simp [resolution, ResolveState.withWrite, ResolveState.withCatalog, Except.map, bind, Except.bind] at found
  | ok pair =>
    obtain ⟨statement, catalog⟩ := pair
    rcases resolveDropTable_shape resolution with ⟨positions', rules', rfl⟩ | ⟨error, rfl⟩
    · rw [resolution, ResolveState.withWrite_drop_off context state _ _ _ off] at found
      simp only [Except.ok.injEq, Prod.mk.injEq, Resolved.Statement.drop.injEq] at found
      obtain ⟨⟨rfl, rfl⟩, -⟩ := found
      exact resolveDropTable_drop resolution
    · rw [resolution, ResolveState.withWrite_prepareError_off context state _ _ off] at found
      simp at found

/-- For every catalog, two names that find tables, and the names that differ after folding: the objects
that DROP TABLE removes with the first table ({name}`Catalog.tableObjects`) do not include the position
of the second table. In plain words, DROP TABLE of one table leaves every table of another name in the
catalog. Proof sketch: a listed position is the table itself, which would give the two names the same
object, or an index or a trigger, which is no table. -/
theorem Catalog.tableObjects_not_contains {catalog : Catalog} {dropped other : Identifier}
    {droppedAt otherAt : Nat} {droppedTable otherTable : CatalogTable}
    (droppedFound : catalog.findTable dropped = some (droppedAt, droppedTable))
    (otherFound : catalog.findTable other = some (otherAt, otherTable))
    (different : other.folded ≠ dropped.folded) :
    (catalog.tableObjects droppedAt).contains otherAt = false := by
  obtain ⟨droppedObject, droppedPlace, droppedEntry, droppedName⟩ := Catalog.findTable_some _ _ _ _ droppedFound
  obtain ⟨otherObject, otherPlace, otherEntry, otherName⟩ := Catalog.findTable_some _ _ _ _ otherFound
  rw [Bool.eq_false_iff]
  intro contained
  have member : otherAt ∈ catalog.tableObjects droppedAt := by simpa using contained
  unfold Catalog.tableObjects at member
  rw [List.mem_cons] at member
  rcases member with same | listed
  · subst same
    rw [droppedPlace] at otherPlace
    cases otherPlace
    exact different (otherName.symm.trans droppedName)
  · obtain ⟨⟨object, place⟩, inside, result⟩ := List.mem_filterMap.mp listed
    have atPlace := List.mem_zipIdx_iff_getElem?.mp inside
    simp only at atPlace
    have result' : place = otherAt := by
      cases hentry : object.entry <;> simp_all <;> split at result <;> simp_all
    subst result'
    rw [otherPlace] at atPlace
    cases atPlace
    simp [otherEntry] at result

end Belay.Sqlite.Model
