import Belay.Sqlite.Model.NormalizedFieldResolution

set_option doc.verso true

/-! The backfill's exact assignment and absence of row programs. The trigger
premise concerns the catalog after adding the column, because previously
unknown UPDATE OF names can become meaningful at that point. -/

namespace Belay.Sqlite.Model.NormalizedField

/-- Lowercase of a found original column mentions that row, so assignment keeps
the expression instead of folding it as a constant. Proof sketch: the single
source contributes the known column match. -/
private theorem lower_mentions {position : Option Nat} {tableName name : Identifier}
    {columns : List CatalogColumn} {rowid : Bool} {source : Nat} (found : columnPosition columns name = some source) :
    mentionsColumn (Scope.singleAt position tableName columns rowid)
      (.call "lower" [.identifier name .none]) = true := by
  simp [mentionsColumn, mentionsColumnIn, Scope.matches, Scope.singleAt, found]

/-- On a table with the fresh plain TEXT field appended, any successful backfill
resolution assigns exactly that field to lowercase of the original named
column. Restriction branches do not satisfy the resolution premise. The table's
other keys, indexes and constraints are retained. Proof sketch: identify the
two column positions and the scalar operand; the remaining checks either
refuse resolution or leave this assignment unchanged. -/
theorem update_resolution {context : ResolveContext} {catalog : Catalog}
    {tableName name sourceName : Identifier} {position source : Nat} {table : CatalogTable}
    {resolved : Resolved.Statement} {next : Catalog}
    (found : catalog.findTable tableName =
      some (position, { table with columns := table.columns ++ [textColumn name table.strict] }))
    (fresh : columnPosition table.columns name = none)
    (sourceFound : columnPosition table.columns sourceName = some source)
    (ok : resolveUpdate context catalog tableName
      [(name, .call "lower" [.identifier sourceName .none])] none [] [] {} = .ok (resolved, next)) :
    resolved = .update position [(table.columns.length, .scalar .lower (.cons (.column source) .nil))]
      none [] [] none ∧ next = catalog := by
  have old := columnPosition_append sourceFound [textColumn name table.strict]
  have added := columnPosition_new fresh table.strict
  have mentions := lower_mentions (position := some position) (tableName := tableName)
    (rowid := !table.withoutRowid) old
  have operand := resolve_lower_column_at (dqs := context.profile.dqsDml) (position := some position)
    (tableName := tableName) (rowid := !table.withoutRowid) old
  have generated : ((table.columns ++ [textColumn name table.strict])[table.columns.length]?.bind
      (·.generated)).isSome = false := by
    rw [List.getElem?_append_right (Nat.le_refl table.columns.length), Nat.sub_self]
    rfl
  have assignment (keys : List Nat) (failure : Identifier → ValueIssue) (rowid : Option (Option Nat))
      (item : Nat) : (resolveAssignmentTraced context.profile.dqsDml
        (Scope.singleAt (some position) tableName (table.columns ++ [textColumn name table.strict])
          !table.withoutRowid)
        {} keys failure rowid item [] (name, .call "lower" [.identifier sourceName .none])).drop =
      if keys.contains table.columns.length then .error (.restriction [item, 1] .rowDependentKey)
      else .ok (table.columns.length, .scalar .lower (.cons (.column source) .nil)) := by
    simp only [resolveAssignmentTraced, traced_drop, resolveOperandTraced_drop, assignedPosition, List.append_nil,
      operand, Except.mapError, bind, Scope.columns_singleAt, added, generated, Bool.false_eq_true, ↓reduceIte,
      mentions, Bool.true_and, Bool.not_true, Bool.false_and, assignedExpression, Bool.true_or]
  cases keyed : ((catalog.uniqueKeys position
      { table with columns := table.columns ++ [textColumn name table.strict] }).flatMap
        (·.reads (table.columns ++ [textColumn name table.strict]).length)).contains table.columns.length <;>
    simp only [resolveUpdate, resolveUpdateTraced, traced_drop, found, Option.map_none, Option.getD_none, resolveAll,
      resolveAllFrom, assignment, keyed, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure, resolveReturningTraced, resolveWriteFilterTraced, Except.map, List.any_nil,
      issueResolution, restrict] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl⟩)
    | cases ok

/-- A backfill UPDATE has no resolved trigger programs when its exact event
fires no trigger in the supplied catalog and both foreign keys and recursive
triggers are off. The premise checks trigger selection, including UPDATE OF
names, rather than trigger conditions or final row contents. Proof sketch:
the initial request has no fired program and no generated request, so its
existing bounded closure ends with an empty list. -/
theorem backfill_programs_empty (context : ResolveContext) (catalog : Catalog)
    (position width source : Nat)
    (noneFiring : catalog.triggersFiring
      { table := position, event := .update (some [width]) } = []) :
    triggerPrograms context catalog false false
      (.update position [(width, .scalar .lower (.cons (.column source) .nil))] none [] [] none) =
      .ok (.ok []) := by
  have positive : 0 < closureFuel catalog := by unfold closureFuel; omega
  obtain ⟨fuel, equal⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  unfold triggerPrograms
  rw [show closureFuel catalog = fuel + 1 from equal]
  cases fuel <;>
    simp [Resolved.Statement.fireRequest, Resolved.Statement.updatesOnConflict,
      triggerClosure, Catalog.firedTriggers, noneFiring,
      FireRequest.followUps, FireRequest.replaceRequests, pure, Except.pure, bind, Except.bind]

/-- With both settings off and no firing trigger for the backfill event, the
write-state wrapper keeps its plain UPDATE form and only carries its catalog.
It adds no foreign-key or trigger plan. Proof sketch: the checked empty program
list and the absent foreign-key checks select the wrapper's plain branch. -/
theorem withWrite_backfill (context : ResolveContext) (state : ResolveState)
    (position width source : Nat) (foreign : state.foreignKeys = false)
    (recursive : state.recursiveTriggers = false)
    (noneFiring : state.catalog.triggersFiring
      { table := position, event := .update (some [width]) } = []) :
    state.withWrite context (.ok
      (.update position [(width, .scalar .lower (.cons (.column source) .nil))] none [] [] none,
        state.catalog)) =
      .ok (.update position [(width, .scalar .lower (.cons (.column source) .nil))] none [] [] none, state) := by
  simp only [ResolveState.withWrite, ResolveState.withCatalog, Except.map, bind, Except.bind,
    pure, Except.pure, foreign, recursive, Bool.false_eq_true, ↓reduceIte,
    backfill_programs_empty context state.catalog position width source noneFiring]
  have noRead : (Resolved.Statement.update position
      [(width, .scalar .lower (.cons (.column source) .nil))] none [] [] none).readsCounterInWrite false = false := rfl
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or, noRead, ↓reduceIte, Bool.false_eq_true]
  cases state
  cases foreign
  cases recursive
  rfl

/-- Any successful statement resolution of this backfill is the plain UPDATE
of the appended column, with unchanged resolution state. The source and fresh
column names must bind as stated, both settings are off, and the exact UPDATE
event must fire no trigger in this extended catalog. Restriction outcomes do
not satisfy the premise. Proof sketch: the empty subquery list leaves ordinary
UPDATE resolution, whose exact assignment and empty rule wrapper were proved
above. -/
theorem backfill_resolution {context : ResolveContext} {state after : ResolveState}
    {tableName name sourceName : Identifier} {position source : Nat} {table : CatalogTable}
    {resolved : Resolved.Statement}
    (found : state.catalog.findTable tableName =
      some (position, { table with columns := table.columns ++ [textColumn name table.strict] }))
    (fresh : columnPosition table.columns name = none)
    (sourceFound : columnPosition table.columns sourceName = some source)
    (foreign : state.foreignKeys = false) (recursive : state.recursiveTriggers = false)
    (noneFiring : state.catalog.triggersFiring
      { table := position, event := .update (some [table.columns.length]) } = [])
    (ok : resolveStatement context state
      (.update tableName [(name, .call "lower" [.identifier sourceName .none])] none [] []) =
        .ok (resolved, after)) :
    resolved = .update position [(table.columns.length, .scalar .lower (.cons (.column source) .nil))]
      none [] [] none ∧ after = state := by
  have bare : resolveStatement context state
      (.update tableName [(name, .call "lower" [.identifier sourceName .none])] none [] []) =
      state.withWrite context (resolveUpdate context state.catalog tableName
        [(name, .call "lower" [.identifier sourceName .none])] none [] [] {}) := by
    have notView := Catalog.findView_none_of_table found
    have noCopies : querySourceCopiesNeeded state.catalog commonTablePlaceholder [] = false := by
      simp [querySourceCopiesNeeded, Syntax.TableReference.namesStoredView, commonTablePlaceholder]
    simp only [statement_arms, resolveCommonTableWrite_arm, Bool.not_false, ↓reduceIte,
      resolveWriteSubqueries_arm, found, Option.map_some, Option.getD_some, notView, Option.isSome_none,
      Bool.false_eq_true, noCopies]
    rfl
  rw [bare] at ok
  cases body : resolveUpdate context state.catalog tableName
      [(name, .call "lower" [.identifier sourceName .none])] none [] [] {} with
  | error issue => simp [body, ResolveState.withWrite, ResolveState.withCatalog, Except.map, bind, Except.bind] at ok
  | ok pair =>
    obtain ⟨bodyStatement, bodyCatalog⟩ := pair
    obtain ⟨rfl, rfl⟩ := update_resolution found fresh sourceFound body
    rw [body, withWrite_backfill context state position table.columns.length source
      foreign recursive noneFiring] at ok
    cases ok
    exact ⟨rfl, rfl⟩

end Belay.Sqlite.Model.NormalizedField
