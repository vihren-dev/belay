import Belay.Sqlite.Model.BackfillUpdateResolution
import Belay.Sqlite.Model.SimpleStatementResolution
import Belay.Sqlite.Model.Resolution.SyntaxReindexLaws

set_option doc.verso true

/-! The resolution of the whole statement that backfills an appended column (ADR 0017, S6). The
statement is {lit}`UPDATE t SET c = e` with no filter, no RETURNING clause and no subquery. With foreign
keys and recursive triggers off, and no trigger that the exact UPDATE event fires, it resolves to the plain
UPDATE and carries no foreign-key or trigger plan. The trigger premise concerns the catalog after ADD
COLUMN, because the UPDATE OF names of a trigger can become meaningful at that point. -/

namespace Belay.Sqlite.Model

/-- For every context, catalog, table position, width of the table with the appended column, assigned
expression and update that fires no trigger in the catalog: the backfill UPDATE has no resolved trigger
programs when both foreign keys and recursive triggers are off. The premise checks the trigger selection,
including UPDATE OF names, and not the trigger conditions or the final row contents. The expression does
not matter, because trigger selection reads only the written column. Proof sketch: the initial request has
no fired program and no generated request, so its existing bounded closure ends with an empty list. -/
theorem backfill_programs_empty (context : ResolveContext) (catalog : Catalog)
    (position width : Nat) (assigned : Resolved.Expr)
    (noneFiring : catalog.triggersFiring { table := position, event := .update (some [width]) } = []) :
    triggerPrograms context catalog false false
      (.update position [(width, assigned)] none [] [] none) = .ok (.ok []) := by
  have positive : 0 < closureFuel catalog := by unfold closureFuel; omega
  obtain ⟨fuel, equal⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  unfold triggerPrograms
  rw [show closureFuel catalog = fuel + 1 from equal]
  cases fuel <;>
    simp [Resolved.Statement.fireRequest, Resolved.Statement.updatesOnConflict,
      triggerClosure, Catalog.firedTriggers, noneFiring,
      FireRequest.followUps, FireRequest.replaceRequests, pure, Except.pure, bind, Except.bind]

/-- For every state, position, width and assigned expression, with both settings off and no trigger firing
for the backfill event, the write-state wrapper keeps the plain UPDATE form and only carries its catalog.
It adds no foreign-key or trigger plan. A plain UPDATE never reads a counter in a write that runs no other
rows. Proof sketch: the checked empty program list and the absent foreign-key checks select the plain
branch of the wrapper. -/
theorem withWrite_backfill (context : ResolveContext) (state : ResolveState)
    (position width : Nat) (assigned : Resolved.Expr) (foreign : state.foreignKeys = false)
    (recursive : state.recursiveTriggers = false)
    (noneFiring : state.catalog.triggersFiring { table := position, event := .update (some [width]) } = []) :
    state.withWrite context (.ok (.update position [(width, assigned)] none [] [] none, state.catalog)) =
      .ok (.update position [(width, assigned)] none [] [] none, state) := by
  simp only [ResolveState.withWrite, ResolveState.withCatalog, Except.map, bind, Except.bind,
    pure, Except.pure, foreign, recursive, Bool.false_eq_true, ↓reduceIte,
    backfill_programs_empty context state.catalog position width assigned noneFiring]
  have noRead : (Resolved.Statement.update position [(width, assigned)] none [] [] none).readsCounterInWrite
      false = false := by
    simp [Resolved.Statement.readsCounterInWrite]
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or, noRead, ↓reduceIte, Bool.false_eq_true]
  cases state
  cases foreign
  cases recursive
  rfl

/-- For every state whose catalog finds the table with the appended column, every written value that
resolves in the scope of that table, and every successful statement resolution of
{lit}`UPDATE t SET name = value` with no filter, RETURNING clause or subquery: the statement is the plain
UPDATE of the appended column with the resolved value ({name}`assignedExpression`), and the resolution
state is unchanged. The name must resolve to the appended column, that column must have no generated
expression, both settings are off, and the exact UPDATE event fires no trigger in this extended catalog.
Restriction outcomes do not satisfy the premise. Proof sketch: the empty subquery list leaves ordinary
UPDATE resolution ({name}`backfillUpdate_resolution`) under the write wrapper ({name}`withWrite_backfill`). -/
theorem backfill_resolution {context : ResolveContext} {state after : ResolveState}
    {tableName name : Identifier} {value : Syntax.Expr} {position : Nat} {table : CatalogTable}
    {column : CatalogColumn} {derived : Resolved.Expr} {affinity : Option Affinity}
    {resolved : Resolved.Statement}
    (found : state.catalog.findTable tableName = some (position, { table with columns := table.columns ++ [column] }))
    (added : columnPosition (table.columns ++ [column]) name = some table.columns.length)
    (newPlain : column.generated = none)
    (operand : resolveOperand context.profile.dqsDml
      (backfillScope position tableName table column) {} true value =
        .ok (derived, affinity))
    (foreign : state.foreignKeys = false) (recursive : state.recursiveTriggers = false)
    (noneFiring : state.catalog.triggersFiring
      { table := position, event := .update (some [table.columns.length]) } = [])
    (ok : resolveStatement context state (.update tableName [(name, value)] none [] []) = .ok (resolved, after)) :
    resolved = .update position [(table.columns.length, assignedExpression
      (backfillScope position tableName table column)
      table.columns.length value derived)] none [] [] none ∧ after = state := by
  have bare : resolveStatement context state (.update tableName [(name, value)] none [] []) =
      state.withWrite context (resolveUpdate context state.catalog tableName [(name, value)] none [] [] {}) := by
    have notView := Catalog.findView_none_of_table found
    have noCopies : querySourceCopiesNeeded state.catalog commonTablePlaceholder [] = false := by
      simp [querySourceCopiesNeeded, Syntax.TableReference.namesStoredView, commonTablePlaceholder]
    simp only [statement_arms, resolveCommonTableWrite_arm, Bool.not_false, ↓reduceIte,
      resolveWriteSubqueries_arm, found, Option.map_some, Option.getD_some, notView, Option.isSome_none,
      Bool.false_eq_true, noCopies, List.map_cons, List.map_nil, Syntax.Expr.reindex_id, Option.map_none]
    rfl
  rw [bare] at ok
  cases body : resolveUpdate context state.catalog tableName [(name, value)] none [] [] {} with
  | error issue => simp [body, ResolveState.withWrite, ResolveState.withCatalog, Except.map, bind, Except.bind] at ok
  | ok pair =>
    obtain ⟨bodyStatement, bodyCatalog⟩ := pair
    obtain ⟨rfl, rfl⟩ := backfillUpdate_resolution found added newPlain operand body
    rw [body, withWrite_backfill context state position table.columns.length _ foreign recursive noneFiring] at ok
    cases ok
    exact ⟨rfl, rfl⟩

end Belay.Sqlite.Model
